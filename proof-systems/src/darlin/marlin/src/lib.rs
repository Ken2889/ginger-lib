//! A crate for [Coboundary Marlin], a variant of the [Marlin] zk-SNARK.
//! The SNARK is obtained from the interactive protocol by Fiat-Shamir transforming
//! the "compiled" algebraic oracle proof, in which oracles are instantiated by
//! a secure polynomial commitment scheme.
//!
//! This implementation is based on the Marlin implementation from [arkworks], using
//! the modifications as described in [HGB].
//!
//! [Coboundary Marlin]: https://eprint.iacr.org/2021/930
//! [Marlin]: https://eprint.iacr.org/2019/1047
//! [HGB]: https://eprint.iacr.org/2021/930
//! [arkworks]: http://github.com/arkworks-rs/marlin
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_imports, unused_mut, missing_docs)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]
#![allow(
    clippy::upper_case_acronyms,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::try_err,
    clippy::map_collect_result_unit,
    clippy::not_unsafe_ptr_arg_deref,
    clippy::suspicious_op_assign_impl,
    clippy::assertions_on_constants
)]

#[macro_use]
extern crate bench_utils;

use algebra::Group;
use algebra::{CanonicalSerialize, serialize_no_metadata};
use digest::Digest;
use poly_commit::{
    evaluate_query_map_to_vec, Evaluations, LabeledRandomness, PCKey, QueryMap,
};
use poly_commit::{optional_rng::OptionalRng, LabeledCommitment, PolynomialCommitment};
use r1cs_core::ConstraintSynthesizer;
use rand_core::RngCore;
use std::marker::PhantomData;

use std::{
    string::{String, ToString},
    vec::Vec,
};

use fiat_shamir::{FiatShamirRng, FiatShamirRngSeed};

mod error;
pub use error::*;

mod data_structures;
pub use data_structures::*;

pub mod iop;
pub use iop::IOP;

#[cfg(test)]
mod test;

/// A helper struct to bundle the Coboundary Marlin functions for setup, prove and
/// verify.
///
/// Coboundary Marlin is an argument for satifiability of an R1CS over a prime
/// field `F` and uses a polynomial commitment scheme `PC` for
/// polynomials over that field and a digest `D` for the Fiat-Shamir transform.
pub struct Marlin<G: Group, PC: PolynomialCommitment<G>>(
    #[doc(hidden)] PhantomData<G>,
    #[doc(hidden)] PhantomData<PC>,
);

impl<'a, G: Group, PC: PolynomialCommitment<G>> Marlin<G, PC> {
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"COBOUNDARY-MARLIN-2021";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup<D: Digest>(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        zk: bool,
    ) -> Result<(PC::CommitterKey, PC::VerifierKey), Error<PC::Error>> {
        let max_degree =
            IOP::<G::ScalarField>::max_degree(num_constraints, num_variables, num_non_zero, zk)?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
            max_degree, num_constraints, num_variables, num_non_zero,
        )
        });

        let srs = PC::setup::<D>(max_degree).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// The circuit-specific setup. Given a circuit `c` and a committer_key of the polynomial
    /// commitment scheme, generate the key material for the circuit. The latter is split into
    /// a prover key and a verifier key.
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<G::ScalarField>, D: Digest>(
        committer_key: &PC::CommitterKey,
        c: C,
    ) -> Result<(ProverKey<G, PC>, VerifierKey<G, PC>), Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        let index = IOP::<G::ScalarField>::index(c)?;

        end_timer!(index_time);

        let commit_time = start_timer!(|| "Commit to index polynomials");

        let (index_comms, index_comm_rands): (_, _) =
            PC::commit_many(committer_key, index.iter(), None).map_err(Error::from_pc_err)?;
        end_timer!(commit_time);

        let index_comms = index_comms
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();

        let vk_hash = D::digest(&serialize_no_metadata![index.index_info, index_comms]
            .map_err(|e| {
                Error::Other(format!("Unable to serialize vk elements: {:?}", e))
            })?)
            .as_ref()
            .to_vec();

        let index_vk = VerifierKey {
            index_info: index.index_info,
            index_comms,
            vk_hash,
        };

        let index_pk = ProverKey {
            index,
            index_comm_rands,
            index_vk: index_vk.clone(),
        };

        Ok((index_pk, index_vk))
    }

    /// Produce a zkSNARK asserting given a constraint system `c` over a prime order field `F`
    pub fn prove<C: ConstraintSynthesizer<G::ScalarField>>(
        index_pk: &ProverKey<G, PC>,
        pc_pk: &PC::CommitterKey,
        c: C,
        zk: bool,
        zk_rng: Option<&mut dyn RngCore>,
    ) -> Result<Proof<G, PC>, Error<PC::Error>> {
        if zk_rng.is_some() && !zk || zk_rng.is_none() && zk {
            return Err(Error::Other("If ZK is enabled, a RNG must be passed (and viceversa); conversely, if ZK is disabled, a RNG must NOT be passed (and viceversa)".to_owned()));
        }

        let zk_rng = &mut OptionalRng(zk_rng);
        let prover_time = start_timer!(|| "Marlin::Prover");

        // prover precomputations
        let prover_init_state = IOP::prover_init(&index_pk.index, c)?;
        let public_input = prover_init_state.public_input();

        // initialize the Fiat-Shamir rng.
        let fs_rng_init_seed = {
            let mut seed_builder = FiatShamirRngSeed::new();
            seed_builder
                .add_bytes(&Self::PROTOCOL_NAME)?
                .add_bytes(&pc_pk.get_hash())?;
            seed_builder.finalize()?
        };

        let mut fs_rng = PC::RandomOracle::from_seed(fs_rng_init_seed)?;
        fs_rng.record::<G::BaseField, _>(index_pk.index_vk.get_hash())?;
        fs_rng.record(public_input)?;

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_first_oracles, prover_state) =
            IOP::prover_first_round(prover_init_state, zk, zk_rng).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) =
            PC::commit_many(pc_pk, prover_first_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        // record the prove oracles by the Fiat-Shamir rng
        fs_rng.record::<G::BaseField, _>(first_comms
            .iter()
            .map(|labeled_comm| labeled_comm.commitment().clone())
            .collect::<Vec<_>>()
        )?;

        let (verifier_first_msg, verifier_state) =
            IOP::verifier_first_round(index_pk.index_vk.index_info, &mut fs_rng)?;

        /*  Second round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_second_oracles, prover_state) =
            IOP::prover_second_round(&verifier_first_msg, prover_state, zk, zk_rng).map_err(
                |e| {
                    end_timer!(prover_time);
                    e
                },
            )?;

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_comms, second_comm_rands) =
            PC::commit_many(pc_pk, prover_second_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        // record the prove oracles by the Fiat-Shamir rng
        fs_rng.record(second_comms
            .iter()
            .map(|labeled_comm| labeled_comm.commitment().clone())
            .collect::<Vec<_>>()
        )?;

        let (verifier_second_msg, verifier_state) =
            IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let prover_third_oracles = IOP::prover_third_round(&verifier_second_msg, prover_state)
            .map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_comms, third_comm_rands) =
            PC::commit_many(pc_pk, prover_third_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        // again, record the prove oracles by the Fiat-Shamir rng
        fs_rng.record(third_comms
            .iter()
            .map(|labeled_comm| labeled_comm.commitment().clone())
            .collect::<Vec<_>>()
        )?;

        /* Preparations before entering the batch evaluation proof
         */

        let verifier_state = IOP::verifier_third_round(verifier_state, &mut fs_rng)?;

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = index_pk
            .index
            .iter()
            .chain(prover_first_oracles.iter())
            .chain(prover_second_oracles.iter())
            .chain(prover_third_oracles.iter())
            .collect();

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
            second_comms.iter().map(|p| p.commitment().clone()).collect(),
            third_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];

        // Gather commitment randomness together.
        let comm_rands: Vec<LabeledRandomness<PC::Randomness>> = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .collect();

        // Set up the IOP verifier's query set.
        let (query_map, _) = IOP::verifier_query_map(verifier_state)?;

        // Compute the queried values
        let eval_time = start_timer!(|| "Evaluating polynomials over query map");

        let mut evaluations = evaluate_query_map_to_vec(polynomials.clone(), &query_map);

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations
            .into_iter()
            .map(|x| x.1)
            .collect::<Vec<G::ScalarField>>();
        end_timer!(eval_time);

        // record the evaluation claims.
        fs_rng.record(evaluations.clone())?;

        /* The non-interactive batch evaluation proof for the polynomial commitment scheme,
        We pass the Fiat-Shamir rng.
        */

        let opening_time = start_timer!(|| "Compute opening proof");
        let pc_proof = PC::multi_point_multi_poly_open(
            pc_pk,
            polynomials.clone(),
            &query_map,
            &mut fs_rng,
            &comm_rands,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(opening_time);

        let proof = Proof::new(commitments, evaluations, pc_proof);

        end_timer!(prover_time);

        proof.print_size_info();
        Ok(proof)
    }

    /// Verify a proof as produced by `fn prove()`.
    /// Internally, the function calls `fn verify_iop` and `fn verify_opening`.
    pub fn verify(
        index_vk: &VerifierKey<G, PC>,
        pc_vk: &PC::VerifierKey,
        public_input: &[G::ScalarField],
        proof: &Proof<G, PC>,
    ) -> Result<bool, Error<PC::Error>> {
        let verifier_time = start_timer!(|| "Marlin Verifier");

        // The Fiat-Shamir verifier  for the algebraic oracle proof part.
        let iop_result = Self::verify_iop(pc_vk, index_vk, &public_input, proof);

        if iop_result.is_err() {
            end_timer!(verifier_time);
            eprintln!("IOP Verification failed: {:?}", iop_result.err());
            return Ok(false);
        }

        let (query_map, evaluations, commitments, mut fs_rng) = iop_result.unwrap();

        // Check opening proof
        let opening_result = Self::verify_opening(
            pc_vk,
            proof,
            commitments,
            query_map,
            evaluations,
            &mut fs_rng,
        );

        if opening_result.is_err() {
            end_timer!(verifier_time);
            eprintln!(
                "Opening proof Verification failed: {:?}",
                opening_result.err()
            );
            return Ok(false);
        }

        end_timer!(verifier_time);
        opening_result
    }

    /// The Fiat-Shamir verifier for the algebraic oracle proof of Coboundary Marlin,
    /// without verifying the subsequent batch evaluation proof.
    /// Does all the algebraic checks on the claimed values in a proof, and returns
    ///     - the commitments, query set and evaluation claims, as well as
    ///     - the Fiat-Shamir rng,
    /// as needed for the remaining verification of the dlog opening proof.
    // TODO: By now, the only external call is from the batch verifier for FinalDarlin /
    // SimpleMarlin proofs. Let us think whether serving this functionality as public is a good
    // decision.
    pub fn verify_iop(
        pc_vk: &PC::VerifierKey,
        index_vk: &VerifierKey<G, PC>,
        public_input: &[G::ScalarField],
        proof: &Proof<G, PC>,
    ) -> Result<
        (
            QueryMap<'a, G::ScalarField>,
            Evaluations<'a, G::ScalarField>,
            Vec<LabeledCommitment<PC::Commitment>>,
            PC::RandomOracle,
        ),
        Error<PC::Error>,
    > {
        let iop_verification_time = start_timer!(|| "Verify Sumcheck equations");

        let public_input = public_input.to_vec();

        // initialize the Fiat-Shamir rng.
        let fs_rng_init_seed = {
            let mut seed_builder = FiatShamirRngSeed::new();
            seed_builder
                .add_bytes(&Self::PROTOCOL_NAME)?
                .add_bytes(&pc_vk.get_hash())?;
            seed_builder.finalize()?
        };

        let mut fs_rng = PC::RandomOracle::from_seed(fs_rng_init_seed)?;
        fs_rng.record::<G::BaseField, _>(index_vk.get_hash())?;
        fs_rng.record(public_input.clone())?;

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let first_comms = &proof.commitments[0];
        fs_rng.record(first_comms.clone())?;

        let (_, verifier_state) = IOP::verifier_first_round(index_vk.index_info, &mut fs_rng)?;

        /*  Second round of the compiled and Fiat-Shamir transformed oracle proof-
        The verification of the outer sumcheck equation is postponed to below
        */
        let second_comms = &proof.commitments[1];
        fs_rng.record(second_comms.clone())?;

        let (_, verifier_state) = IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
        The verification of the inner sumcheck equation is postponed to below
        */

        let third_comms = &proof.commitments[2];
        fs_rng.record(third_comms.clone())?;

        let verifier_state = IOP::verifier_third_round(verifier_state, &mut fs_rng)?;

        // Gather commitments in one vector.
        let commitments: Vec<_> = index_vk
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(IOP::<G::ScalarField>::polynomial_labels())
            .map(|(c, l)| LabeledCommitment::new(l, c))
            .collect();

        // Check sumchecks equations
        let (query_map, verifier_state) = IOP::verifier_query_map(verifier_state)?;

        let mut evaluation_keys = Vec::new();
        for (point_label, (_, poly_set)) in query_map.iter() {
            for poly_label in poly_set {
                evaluation_keys.push((poly_label.clone(), point_label.clone()));
            }
        }
        evaluation_keys.sort();

        let mut evaluations = Evaluations::new();
        for (key, &eval) in evaluation_keys.into_iter().zip(proof.evaluations.iter()) {
            evaluations.insert(key, eval);
        }

        let result = IOP::verify_sumchecks(&public_input, &evaluations, &verifier_state);

        if result.is_err() {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(result.unwrap_err()));
        }

        end_timer!(iop_verification_time);

        Ok((query_map, evaluations, commitments, fs_rng))
    }

    /// The remaining check of verifying the batch evaluation proof.
    pub fn verify_opening(
        pc_vk: &PC::VerifierKey,
        proof: &Proof<G, PC>,
        labeled_comms: Vec<LabeledCommitment<PC::Commitment>>,
        query_map: QueryMap<'a, G::ScalarField>,
        evaluations: Evaluations<'a, G::ScalarField>,
        fs_rng: &mut PC::RandomOracle,
    ) -> Result<bool, Error<PC::Error>> {
        let check_time = start_timer!(|| "Check opening proof");

        fs_rng.record(proof.evaluations.clone())?;

        let result = PC::multi_point_multi_poly_verify(
            pc_vk,
            &labeled_comms,
            &query_map,
            &evaluations,
            &proof.pc_proof,
            fs_rng,
        )
        .map_err(Error::from_pc_err);

        end_timer!(check_time);

        result
    }
}
