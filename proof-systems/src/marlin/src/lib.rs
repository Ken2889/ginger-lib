//! A crate for the Marlin preprocessing zkSNARK for R1CS.
//!
//! # Note
//!
//! Currently, Marlin only supports R1CS instances where the number of inputs
//! is the same as the number of constraints (i.e., where the constraint
//! matrices are square). Furthermore, Marlin only supports instances where the
//! public inputs are of size one less than a power of 2 (i.e., 2^n - 1).
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

use algebra::to_bytes;
use algebra::PrimeField;
use algebra::ToBytes;
use digest::Digest;
use poly_commit::{evaluate_query_set_to_vec, Evaluations, LabeledRandomness, QuerySet};
use poly_commit::{
    optional_rng::OptionalRng, LabeledCommitment, PCCommitterKey, PCUniversalParams, PCVerifierKey,
    PolynomialCommitment,
};
use r1cs_core::ConstraintSynthesizer;
use rand_core::RngCore;
use std::marker::PhantomData;

use std::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

use poly_commit::rng::{FiatShamirRng, FiatShamirRngSeed};

mod error;
pub use error::*;

mod data_structures;
pub use data_structures::*;

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
use crate::ahp::indexer::Index;
pub use ahp::AHPForR1CS;
use algebra::get_best_evaluation_domain;

#[cfg(test)]
mod test;

/// The compiled argument system.
pub struct Marlin<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest>(
    #[doc(hidden)] PhantomData<F>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<D>,
);

impl<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest> Marlin<F, PC, D> {
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"COBOUNDARY-MARLIN-2021";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        zk: bool,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>> {
        let max_degree =
            AHPForR1CS::<F>::max_degree(num_constraints, num_variables, num_non_zero, zk)?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
            max_degree, num_constraints, num_variables, num_non_zero,
        )
        });

        let srs = PC::setup(max_degree).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// Wrapper around `AHPForR1CS::index`, for external access
    /// TODO: Find a better name for `index` function and rename this function to `index`
    pub fn get_index_info<C: ConstraintSynthesizer<F>>(c: C) -> Result<Index<F>, Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::index(c)?;

        end_timer!(index_time);

        Ok(index)
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys, already given `index`.
    pub fn circuit_specific_setup(
        committer_key: &PC::CommitterKey,
        index: Index<F>,
    ) -> Result<(ProverKey<F, PC>, VerifierKey<F, PC>), Error<PC::Error>> {
        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (index_comms, index_comm_rands): (_, _) =
            PC::commit(committer_key, index.iter(), None).map_err(Error::from_pc_err)?;
        end_timer!(commit_time);

        let index_comms = index_comms
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();

        let index_vk = VerifierKey {
            index_info: index.index_info,
            index_comms,
        };

        let index_pk = ProverKey {
            index,
            index_comm_rands,
            index_vk: index_vk.clone(),
        };

        Ok((index_pk, index_vk))
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a deterministic algorithm that anyone can rerun.
    pub fn index<C: ConstraintSynthesizer<F>>(
        committer_key: &PC::CommitterKey,
        c: C,
    ) -> Result<(ProverKey<F, PC>, VerifierKey<F, PC>), Error<PC::Error>> {
        let index = Self::get_index_info(c)?;
        Self::circuit_specific_setup(committer_key, index)
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys starting from a SRS. This is a deterministic algorithm that anyone can rerun.
    pub fn trim_and_index<C: ConstraintSynthesizer<F>>(
        srs: &UniversalSRS<F, PC>,
        c: C,
    ) -> Result<
        (
            ProverKey<F, PC>,
            PC::CommitterKey,
            VerifierKey<F, PC>,
            PC::VerifierKey,
        ),
        Error<PC::Error>,
    > {
        let (committer_key, verifier_key) =
            PC::trim(srs, srs.max_degree()).map_err(Error::from_pc_err)?;

        let (index_pk, index_vk) = Self::index(&committer_key, c)?;

        Ok((index_pk, committer_key, index_vk, verifier_key))
    }

    /// Create a zkSNARK asserting that the constraint system is satisfied.
    pub fn prove<C: ConstraintSynthesizer<F>>(
        index_pk: &ProverKey<F, PC>,
        pc_pk: &PC::CommitterKey,
        c: C,
        zk: bool,
        zk_rng: Option<&mut dyn RngCore>,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
        if zk_rng.is_some() && !zk || zk_rng.is_none() && zk {
            return Err(Error::Other("If ZK is enabled, a RNG must be passed (and viceversa); conversely, if ZK is disabled, a RNG must NOT be passed (and viceversa)".to_owned()));
        }

        let zk_rng = &mut OptionalRng(zk_rng);
        let prover_time = start_timer!(|| "Marlin::Prover");
        // Add check that c is in the correct mode.

        let prover_init_state = AHPForR1CS::prover_init(&index_pk.index, c, zk)?;
        let public_input = prover_init_state.public_input();

        let fs_rng_init_seed = {
            let mut seed_builder = <PC::RandomOracle as FiatShamirRng>::Seed::new();
            seed_builder
                .add_bytes(&Self::PROTOCOL_NAME)
                .map_err(Error::from_pc_err)?;
            seed_builder
                .add_bytes(&pc_pk.get_hash())
                .map_err(Error::from_pc_err)?;

            // NOTE: As both vk and public input use constant length encoding of field elements,
            // we can simply apply add_bytes to achieve a one-to-one serialization.
            seed_builder
                .add_bytes(&index_pk.index_vk)
                .map_err(Error::from_pc_err)?;
            seed_builder
                .add_bytes(&public_input)
                .map_err(Error::from_pc_err)?;

            seed_builder.finalize()
        };
        let mut fs_rng = PC::RandomOracle::from_seed(fs_rng_init_seed);

        // --------------------------------------------------------------------
        // First round

        let (prover_first_msg, prover_first_oracles, prover_state) =
            AHPForR1CS::prover_first_round(prover_init_state, zk, zk_rng).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) =
            PC::commit(pc_pk, prover_first_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        fs_rng.absorb(&to_bytes![first_comms, prover_first_msg].unwrap());

        let (verifier_first_msg, verifier_state) =
            AHPForR1CS::verifier_first_round(index_pk.index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let (prover_second_msg, prover_second_oracles, prover_state) =
            AHPForR1CS::prover_second_round(&verifier_first_msg, prover_state, zk, zk_rng)
                .map_err(|e| {
                    end_timer!(prover_time);
                    e
                })?;

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_comms, second_comm_rands) =
            PC::commit(pc_pk, prover_second_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        fs_rng.absorb(&to_bytes![second_comms, prover_second_msg].unwrap());

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let (prover_third_msg, prover_third_oracles) =
            AHPForR1CS::prover_third_round(&verifier_second_msg, prover_state).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_comms, third_comm_rands) =
            PC::commit(pc_pk, prover_third_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        fs_rng.absorb(&to_bytes![third_comms, prover_third_msg].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

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
        let labeled_comms: Vec<_> = index_pk
            .index_vk
            .iter()
            .cloned()
            .zip(&AHPForR1CS::<F>::INDEXER_POLYNOMIALS)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_comms.iter().cloned())
            .chain(second_comms.iter().cloned())
            .chain(third_comms.iter().cloned())
            .collect();

        // Gather commitment randomness together.
        let comm_rands: Vec<LabeledRandomness<PC::Randomness>> = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .collect();

        // Gather prover messages together.
        let prover_messages = vec![prover_first_msg, prover_second_msg, prover_third_msg];

        // Compute the AHP verifier's query set.
        let (query_set, _) = AHPForR1CS::verifier_query_set(verifier_state)?;

        let eval_time = start_timer!(|| "Evaluating polynomials over query set");

        let mut evaluations = evaluate_query_set_to_vec(polynomials.clone(), &query_set);

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations.into_iter().map(|x| x.1).collect::<Vec<F>>();
        end_timer!(eval_time);

        fs_rng.absorb(&evaluations);

        let opening_time = start_timer!(|| "Compute opening proof");
        let pc_proof = PC::batch_open_individual_opening_challenges(
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

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);

        end_timer!(prover_time);

        proof.print_size_info();
        Ok(proof)
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify(
        index_vk: &VerifierKey<F, PC>,
        pc_vk: &PC::VerifierKey,
        public_input: &[F],
        proof: &Proof<F, PC>,
    ) -> Result<bool, Error<PC::Error>> {
        let verifier_time = start_timer!(|| "Marlin Verifier");

        // Check AHP (e.g. sumcheck equations)
        let ahp_result = Self::verify_ahp(pc_vk, index_vk, &public_input, proof);

        if ahp_result.is_err() {
            end_timer!(verifier_time);
            eprintln!("AHP Verification failed: {:?}", ahp_result.err());
            return Ok(false);
        }

        let (query_set, evaluations, commitments, mut fs_rng) = ahp_result.unwrap();

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

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied. Checks only that the sumcheck equations
    /// are satisfied.
    pub fn verify_ahp<'a>(
        pc_vk: &PC::VerifierKey,
        index_vk: &VerifierKey<F, PC>,
        public_input: &[F],
        proof: &Proof<F, PC>,
    ) -> Result<
        (
            QuerySet<'a, F>,
            Evaluations<'a, F>,
            Vec<LabeledCommitment<PC::Commitment>>,
            PC::RandomOracle,
        ),
        Error<PC::Error>,
    > {
        let ahp_verification_time = start_timer!(|| "Verify Sumcheck equations");

        let public_input = {
            let domain_x = match get_best_evaluation_domain::<F>(public_input.len() + 1) {
                Some(v) => v,
                None => return Err(Error::Other("evaluations domains failed".to_owned())),
            };

            let mut unpadded_input = public_input.to_vec();
            unpadded_input.resize(
                std::cmp::max(public_input.len(), domain_x.size() - 1),
                F::zero(),
            );

            unpadded_input
        };

        let fs_rng_init_seed = {
            let mut seed_builder = <PC::RandomOracle as FiatShamirRng>::Seed::new();
            seed_builder
                .add_bytes(&Self::PROTOCOL_NAME)
                .map_err(Error::from_pc_err)?;
            seed_builder
                .add_bytes(&pc_vk.get_hash())
                .map_err(Error::from_pc_err)?;
            // TODO: Shall we decompose this further when passing it to the seed builder ?
            seed_builder
                .add_bytes(&index_vk)
                .map_err(Error::from_pc_err)?;
            // TODO: Shall we decompose this further when passing it to the seed builder ?
            seed_builder
                .add_bytes(&public_input)
                .map_err(Error::from_pc_err)?;
            seed_builder.finalize()
        };
        let mut fs_rng = PC::RandomOracle::from_seed(fs_rng_init_seed);

        // --------------------------------------------------------------------
        // First round

        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms, proof.prover_messages[0]].unwrap());

        let (_, verifier_state) =
            AHPForR1CS::verifier_first_round(index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms, proof.prover_messages[1]].unwrap());

        let (_, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_comms = &proof.commitments[2];
        fs_rng.absorb(&to_bytes![third_comms, proof.prover_messages[2]].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.
        let index_info = index_vk.index_info;
        let degree_bounds = vec![None; index_vk.index_comms.len()]
            .into_iter()
            .chain(AHPForR1CS::prover_first_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_second_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_third_round_degree_bounds(&index_info))
            .collect::<Vec<_>>();

        // Gather commitments in one vector.
        let commitments: Vec<_> = index_vk
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(AHPForR1CS::<F>::polynomial_labels())
            .zip(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        // Check sumchecks equations
        let (query_set, verifier_state) = AHPForR1CS::verifier_query_set(verifier_state)?;

        let mut evaluations = Evaluations::new();
        let mut evaluation_labels = Vec::new();
        for (poly_label, (point_label, point)) in query_set.iter().cloned() {
            evaluation_labels.push(((poly_label, point_label), point));
        }

        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(((q.0).0, q.1), *eval);
        }

        let result = AHPForR1CS::verify_sumchecks(&public_input, &evaluations, &verifier_state);

        if result.is_err() {
            end_timer!(ahp_verification_time);
            return Err(Error::AHPError(result.unwrap_err()));
        }

        end_timer!(ahp_verification_time);

        Ok((query_set, evaluations, commitments, fs_rng))
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied. Checks only that the opening proof is
    /// satisfied.
    pub fn verify_opening<'a>(
        pc_vk: &PC::VerifierKey,
        proof: &Proof<F, PC>,
        labeled_comms: Vec<LabeledCommitment<PC::Commitment>>,
        query_set: QuerySet<'a, F>,
        evaluations: Evaluations<'a, F>,
        fs_rng: &mut PC::RandomOracle,
    ) -> Result<bool, Error<PC::Error>> {
        let check_time = start_timer!(|| "Check opening proof");

        fs_rng.absorb(&proof.evaluations);

        let result = PC::batch_check_individual_opening_challenges(
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
