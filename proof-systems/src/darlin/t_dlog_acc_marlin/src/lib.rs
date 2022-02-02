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

use algebra::{to_bytes, Curve};
use algebra::{Group, ToBytes};
use poly_commit::{evaluate_query_set_to_vec, Evaluations, LabeledRandomness, QuerySet};
use poly_commit::{
    optional_rng::OptionalRng, LabeledCommitment, PCVerifierKey, PolynomialCommitment,
};
use r1cs_core::ConstraintSynthesizer;
use rand_core::RngCore;
use std::marker::PhantomData;

use digest::Digest;
use std::{
    string::{String, ToString},
    vec::Vec,
};

use poly_commit::fiat_shamir_rng::{FiatShamirRng, FiatShamirRngSeed};

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
/// polynomials over that field.
pub struct Marlin<G1: Curve, G2: Curve, D: Digest>(
    #[doc(hidden)] PhantomData<G1>,
    #[doc(hidden)] PhantomData<G2>,
    #[doc(hidden)] PhantomData<D>,
);

impl<G1: Curve, G2: Curve, D: Digest + 'static> Marlin<G1, G2, D> {
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"COBOUNDARY-MARLIN-2021";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup(
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) -> Result<UniversalSRS<G1, PC<G1, D>>, Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>>
    {
        let max_degree = IOP::<G1, G2>::max_degree(num_constraints, num_variables, zk)?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars",
            max_degree, num_constraints, num_variables,
        )
        });

        let srs = PC::<G1, D>::setup(max_degree).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// The circuit-specific setup. Given a circuit `c` and a committer_key of the polynomial
    /// commitment scheme, generate the key material for the circuit. The latter is split into
    /// a prover key and a verifier key.
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<G1::ScalarField>>(
        committer_key: &<PC<G1, D> as PolynomialCommitment<G1>>::CommitterKey,
        c: C,
    ) -> Result<
        (ProverKey<G1, G2, D>, VerifierKey<G1, G2, D>),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        // the setup for now (i.e. without using a "recursive circuit") will
        // call the marlin setup and just use
        //  1. R1CS matrices
        //  2. The commitments of the row(M), col(M), val.row.col(M) (overall
        // 9 group elements)
        // Therefore the key material for t-dlog-acc marlin is
        //  1. prover key: the above key material & the full-length polynomial
        //   (i.e. the coeffs) of the T_eta(alpha',Y) in the prev. acc.
        //   (This poly can be returned by the t-acc verifier?)
        // 2. verifier key: the above key material.
        let index_time = start_timer!(|| "Marlin::Index");

        let index = IOP::<G1, G2>::index(c)?;

        end_timer!(index_time);

        let commit_time = start_timer!(|| "Commit to index polynomials");

        let (index_comms, index_comm_rands): (_, _) =
            <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(committer_key, index.iter(), None)
                .map_err(Error::from_pc_err)?;
        end_timer!(commit_time);

        let index_comms = index_comms
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();

        let index_vk = VerifierKey { index, index_comms };

        let index_pk = ProverKey {
            index_vk: index_vk.clone(),
            index_comm_rands,
        };

        Ok((index_pk, index_vk))
    }

    fn fiat_shamir_rng_init(
        pc_vk: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        index_vk: &VerifierKey<G1, G2, D>,
        public_input: &Vec<G1::ScalarField>,
        inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        dlog_acc: &DualDLogItem<G2, G1>,
    ) -> Result<<PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle, poly_commit::error::Error>
    {
        let fs_rng_init_seed = {
            let mut seed_builder =
                <<PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle as FiatShamirRng>::Seed::new(
                );
            seed_builder.add_bytes(&Self::PROTOCOL_NAME)?;
            seed_builder.add_bytes(&PCVerifierKey::get_hash(pc_vk))?;
            seed_builder.add_bytes(inner_sumcheck_acc)?;
            seed_builder.add_bytes(dlog_acc)?;

            // NOTE: As both vk and public input use constant length encoding of field elements,
            // we can simply apply add_bytes to achieve a one-to-one serialization.
            seed_builder.add_bytes(index_vk)?;
            seed_builder.add_bytes(public_input)?;

            seed_builder.finalize()
        };
        let fs_rng =
            <PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle::from_seed(fs_rng_init_seed);
        Ok(fs_rng)
    }

    /// Produce a zkSNARK asserting given a constraint system `c` over a prime order field `F`
    pub fn prove<C: ConstraintSynthesizer<G1::ScalarField>>(
        index_pk: &ProverKey<G1, G2, D>,
        pc_pk: &<PC<G1, D> as PolynomialCommitment<G1>>::CommitterKey,
        c: C,
        previous_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        zk: bool,
        zk_rng: Option<&mut dyn RngCore>,
    ) -> Result<
        (Proof<G1, G2, D>, DualSumcheckItem<G1, G2>),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        if zk_rng.is_some() && !zk || zk_rng.is_none() && zk {
            return Err(Error::Other("If ZK is enabled, a RNG must be passed (and viceversa); conversely, if ZK is disabled, a RNG must NOT be passed (and viceversa)".to_owned()));
        }

        let zk_rng = &mut OptionalRng(zk_rng);
        let prover_time = start_timer!(|| "Marlin::Prover");

        // prover precomputations
        let prover_init_state =
            IOP::prover_init(&index_pk.index_vk.index, c, previous_inner_sumcheck_acc)?;
        let public_input = prover_init_state.public_input();

        let verifier_init_state = IOP::verifier_init(
            &index_pk.index_vk.index.index_info,
            previous_inner_sumcheck_acc,
        )?;

        let mut fs_rng = Self::fiat_shamir_rng_init(
            pc_pk,
            &index_pk.index_vk,
            &public_input,
            previous_inner_sumcheck_acc,
            previous_dlog_acc,
        )
        .map_err(Error::from_pc_err)?;

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_first_oracles, prover_state) =
            IOP::prover_first_round(prover_init_state, zk, zk_rng).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) = <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(
            pc_pk,
            prover_first_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (verifier_first_msg, verifier_state) =
            IOP::verifier_first_round(verifier_init_state, &mut fs_rng)?;

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
            <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(
                pc_pk,
                prover_second_oracles.iter(),
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (verifier_second_msg, verifier_state) =
            IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_third_oracles, prover_state) =
            IOP::prover_third_round(&verifier_second_msg, prover_state).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_comms, third_comm_rands) = <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(
            pc_pk,
            prover_third_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![third_comms].unwrap());

        let (verifier_third_msg, verifier_state) =
            IOP::verifier_third_round(verifier_state, &mut fs_rng)?;

        /*  Fourth round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_fourth_oracles, prover_state) =
            IOP::prover_fourth_round(&verifier_third_msg, prover_state).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let fourth_round_comm_time = start_timer!(|| "Committing to fourth round polys");
        let (fourth_comms, fourth_comm_rands) =
            <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(
                pc_pk,
                prover_fourth_oracles.iter(),
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?;
        end_timer!(fourth_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![fourth_comms].unwrap());

        let (prover_accumulator_oracles, _) =
            IOP::prover_compute_acc_polys(prover_state).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = prover_first_oracles
            .iter()
            .chain(prover_second_oracles.iter())
            .chain(prover_third_oracles.iter())
            .chain(prover_fourth_oracles.iter())
            .chain(prover_accumulator_oracles.iter())
            .collect();

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
            second_comms.iter().map(|p| p.commitment().clone()).collect(),
            third_comms.iter().map(|p| p.commitment().clone()).collect(),
            fourth_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];

        let mut labeled_comms: Vec<_> = index_pk
            .index_vk
            .iter()
            .cloned()
            .zip(&IOP::<G1, G2>::INDEXER_POLYNOMIALS)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c))
            .chain(first_comms.iter().cloned())
            .chain(second_comms.iter().cloned())
            .chain(third_comms.iter().cloned())
            .chain(fourth_comms.iter().cloned())
            .collect();

        labeled_comms.push(LabeledCommitment::new(
            "t_prime".to_string(),
            previous_inner_sumcheck_acc.1.c.clone(),
        ));

        // Gather commitment randomness together.
        let mut comm_rands: Vec<
            LabeledRandomness<<PC<G1, D> as PolynomialCommitment<G1>>::Randomness>,
        > = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .chain(fourth_comm_rands)
            .collect();

        comm_rands.push(LabeledRandomness::new(
            "t_prime".to_string(),
            <PC<G1, D> as PolynomialCommitment<G1>>::Randomness::zero(),
        ));

        // Set up the IOP verifier's query set.
        let (query_set, _) = IOP::verifier_query_set(verifier_state)?;

        // Compute the queried values
        let eval_time = start_timer!(|| "Evaluating polynomials over query set");

        let mut evaluations = evaluate_query_set_to_vec(polynomials.clone(), &query_set);

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations
            .into_iter()
            .map(|x| x.1)
            .collect::<Vec<G1::ScalarField>>();
        end_timer!(eval_time);

        // absorb the evalution claims.
        fs_rng.absorb(&evaluations);

        /* The non-interactive batch evaluation proof for the polynomial commitment scheme,
        We pass the Fiat-Shamir rng.
        */

        let opening_time = start_timer!(|| "Compute opening proof");
        let pc_proof = PC::multi_point_multi_poly_open(
            pc_pk,
            polynomials.clone(),
            &labeled_comms,
            &query_set,
            &mut fs_rng,
            &comm_rands,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(opening_time);

        let proof = Proof::new(commitments, evaluations, pc_proof);

        let accumulated_sumcheck_acc = SumcheckItem {
            zeta: verifier_third_msg.gamma,
            eta: verifier_first_msg.eta
                + verifier_third_msg.lambda * previous_inner_sumcheck_acc.1.eta,
            c: fourth_comms[0].commitment().clone(),
        };
        let new_inner_sumcheck_acc = DualSumcheckItem(
            accumulated_sumcheck_acc,
            previous_inner_sumcheck_acc.0.clone(),
        );

        end_timer!(prover_time);

        proof.print_size_info();
        Ok((proof, new_inner_sumcheck_acc))
    }

    /// Verify a proof as produced by `fn prove()`.
    /// Internally, the function calls `fn verify_iop` and `fn verify_opening`.
    pub fn verify(
        index_vk: &VerifierKey<G1, G2, D>,
        pc_vk: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        public_input: &[G1::ScalarField],
        previous_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        new_inner_sumcheck_acc: &DualSumcheckItem<G1, G2>,
        proof: &Proof<G1, G2, D>,
    ) -> Result<bool, Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>> {
        let verifier_time = start_timer!(|| "Marlin Verifier");

        // The Fiat-Shamir verifier  for the algebraic oracle proof part.
        let iop_result = Self::verify_iop(
            pc_vk,
            index_vk,
            &public_input,
            previous_inner_sumcheck_acc,
            new_inner_sumcheck_acc,
            proof,
        );

        if iop_result.is_err() {
            end_timer!(verifier_time);
            eprintln!("IOP Verification failed: {:?}", iop_result.err());
            return Ok(false);
        }

        let (query_set, evaluations, commitments, mut fs_rng) = iop_result.unwrap();

        // Check opening proof
        let opening_result = Self::verify_opening(
            pc_vk,
            proof,
            commitments,
            query_set,
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
    pub fn verify_iop<'a>(
        pc_vk: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        index_vk: &VerifierKey<G1, G2, D>,
        public_input: &[G1::ScalarField],
        previous_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        new_inner_sumcheck_acc: &DualSumcheckItem<G1, G2>,
        proof: &Proof<G1, G2, D>,
    ) -> Result<
        (
            QuerySet<'a, G1::ScalarField>,
            Evaluations<'a, G1::ScalarField>,
            Vec<LabeledCommitment<<PC<G1, D> as PolynomialCommitment<G1>>::Commitment>>,
            <PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle,
        ),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        let iop_verification_time = start_timer!(|| "Verify Sumcheck equations");

        let public_input = public_input.to_vec();

        let verifier_init_state =
            IOP::verifier_init(&index_vk.index.index_info, previous_inner_sumcheck_acc)?;

        let mut fs_rng = Self::fiat_shamir_rng_init(
            pc_vk,
            index_vk,
            &public_input,
            previous_inner_sumcheck_acc,
            previous_dlog_acc,
        )
        .map_err(Error::from_pc_err)?;

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (_, verifier_state) = IOP::verifier_first_round(verifier_init_state, &mut fs_rng)?;

        /*  Second round of the compiled and Fiat-Shamir transformed oracle proof-
        The verification of the outer sumcheck equation is postponed to below
        */
        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (_, verifier_state) = IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let third_comms = &proof.commitments[2];
        fs_rng.absorb(&to_bytes![third_comms].unwrap());

        let (_, verifier_state) = IOP::verifier_third_round(verifier_state, &mut fs_rng)?;

        /*  Fourth round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let fourth_comms = &proof.commitments[3];
        fs_rng.absorb(&to_bytes![fourth_comms].unwrap());

        // Gather commitments in one vector.
        let mut commitments: Vec<_> = first_comms
            .into_iter()
            .chain(second_comms)
            .chain(third_comms)
            .chain(fourth_comms)
            .cloned()
            .zip(IOP::<G1, G2>::polynomial_labels())
            .map(|(c, l)| LabeledCommitment::new(l, c))
            .collect();
        commitments.push(LabeledCommitment::new(
            "t_prime".to_string(),
            previous_inner_sumcheck_acc.1.c.clone(),
        ));

        // Check sumchecks equations
        let (query_set, verifier_state) = IOP::verifier_query_set(verifier_state)?;

        let mut evaluations = Evaluations::new();
        let mut evaluation_labels = Vec::new();
        for (poly_label, (point_label, point)) in query_set.iter().cloned() {
            evaluation_labels.push(((poly_label, point_label), point));
        }

        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(((q.0).0, q.1), *eval);
        }

        let result = IOP::verify_sumchecks(&public_input, &evaluations, &verifier_state);

        if result.is_err() {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(result.unwrap_err()));
        }

        let result = IOP::verify_inner_sumcheck_acc(&evaluations, &verifier_state);

        if result.is_err() {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(result.unwrap_err()));
        }

        end_timer!(iop_verification_time);

        Ok((query_set, evaluations, commitments, fs_rng))
    }

    /// The remaining check of verifying the batch evaluation proof.
    pub fn verify_opening<'a>(
        pc_vk: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        proof: &Proof<G1, G2, D>,
        labeled_comms: Vec<LabeledCommitment<<PC<G1, D> as PolynomialCommitment<G1>>::Commitment>>,
        query_set: QuerySet<'a, G1::ScalarField>,
        evaluations: Evaluations<'a, G1::ScalarField>,
        fs_rng: &mut <PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle,
    ) -> Result<bool, Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>> {
        let check_time = start_timer!(|| "Check opening proof");

        fs_rng.absorb(&proof.evaluations);

        let result = PC::multi_point_multi_poly_verify(
            pc_vk,
            &labeled_comms,
            &query_set,
            &evaluations,
            &proof.pc_proof,
            fs_rng,
        )
        .map_err(Error::from_pc_err);

        end_timer!(check_time);

        result
    }
}