//! Module implementing the gadgets related to the Marlin verifier
//!

use crate::constraints::data_structures::{ProofGadget, VerifierKeyGadget};
use crate::constraints::iop::IOPVerificationGadget;
use crate::{Marlin, IOP};
use algebra::EndoMulCurve;
use fiat_shamir::constraints::FiatShamirRngGadget;
use fiat_shamir::FiatShamirRngSeed;
use poly_commit::constraints::PolynomialCommitmentVerifierGadget;
use poly_commit::{Evaluations, LabeledCommitmentGadget, PCKey, PolynomialCommitment, QueryMap};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::groups::{EndoMulCurveGadget, GroupGadget};
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use r1cs_std::ToBitsGadget;
use std::marker::PhantomData;

/// Data structures for Marlin verifier gadget
pub mod data_structures;
/// IOP for Marlin verifier gadget
pub mod iop;

pub mod polynomials;
mod test;

pub struct MarlinVerifierGadget<G, GG, PC, PCG> {
    _g: PhantomData<G>,
    _gg: PhantomData<GG>,
    _pc: PhantomData<PC>,
    _pcg: PhantomData<PCG>,
}

impl<G, GG, PC, PCG> MarlinVerifierGadget<G, GG, PC, PCG>
where
    G: EndoMulCurve,
    GG: EndoMulCurveGadget<G, G::BaseField>
        + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
{
    pub const PROTOCOL_NAME: &'static [u8] = Marlin::<G, PC>::PROTOCOL_NAME;

    pub fn verify_iop<'a, CS: ConstraintSystemAbstract<G::BaseField>>(
        mut cs: CS,
        pc_vk: &PC::VerifierKey,
        index_vk: &VerifierKeyGadget<G, PC, PCG>,
        public_input: &[NonNativeFieldGadget<G::ScalarField, G::BaseField>],
        proof: &ProofGadget<G, PC, PCG>,
    ) -> Result<
        (
            QueryMap<'a, NonNativeFieldGadget<G::ScalarField, G::BaseField>>,
            Evaluations<'a, NonNativeFieldGadget<G::ScalarField, G::BaseField>>,
            Vec<LabeledCommitmentGadget<G::BaseField, PC::Commitment, PCG::CommitmentGadget>>,
            PCG::RandomOracleGadget,
        ),
        SynthesisError,
    > {
        // Check commitment to the input poly
        let one_ins = NonNativeFieldGadget::one(cs.ns(|| "pub ins 1"))?;
        let formatted_public_input = {
            let mut res = vec![one_ins];
            res.extend_from_slice(public_input);
            res
        };

        let x_poly_comm = Self::compute_commit_from_lagrange_representation(
            cs.ns(|| "enforce x_poly commitment"),
            &index_vk.lagrange_comms,
            &formatted_public_input,
        )
        .map_err(|err| SynthesisError::Other(err.to_string()))?;

        // initialize the Fiat-Shamir rng.
        let fs_rng_init_seed = {
            let mut seed_builder = FiatShamirRngSeed::new();
            seed_builder
                .add_bytes(&Self::PROTOCOL_NAME)
                .map_err(|err| SynthesisError::Other(err.to_string()))?
                .add_bytes(&pc_vk.get_hash())
                .map_err(|err| SynthesisError::Other(err.to_string()))?;
            seed_builder
                .finalize()
                .map_err(|err| SynthesisError::Other(err.to_string()))?
        };

        let mut fs_rng = PCG::RandomOracleGadget::init_from_seed(
            cs.ns(|| "init Fiat-Shamir RNG"),
            fs_rng_init_seed,
        )?;
        fs_rng.enforce_record(cs.ns(|| "absorb index_vk hash"), index_vk.get_hash())?;
        fs_rng.enforce_record(cs.ns(|| "absorb x_poly commitment"), x_poly_comm.clone())?;

        let init_comms = vec![x_poly_comm.clone()];
        let first_comms = proof.commitments[0].clone();
        fs_rng.enforce_record(
            cs.ns(|| "enforce absorb first round commitments"),
            first_comms.clone(),
        )?;

        let (_, verifier_state) = IOPVerificationGadget::<G, GG>::verifier_first_round(
            cs.ns(|| "first round"),
            &index_vk.index_info,
            &mut fs_rng,
        )?;

        let second_comms = proof.commitments[1].clone();
        fs_rng.enforce_record(
            cs.ns(|| "enforce absorb second round commitments"),
            second_comms.clone(),
        )?;

        let (_, verifier_state) = IOPVerificationGadget::<G, GG>::verifier_second_round(
            cs.ns(|| "second round"),
            verifier_state,
            &mut fs_rng,
        )?;

        let third_comms = proof.commitments[2].clone();
        fs_rng.enforce_record(
            cs.ns(|| "enforce absorb third round commitments"),
            third_comms.clone(),
        )?;

        let (_, verifier_state) = IOPVerificationGadget::<G, GG>::verifier_third_round(
            cs.ns(|| "third round"),
            verifier_state,
            &mut fs_rng,
        )?;

        let (query_map, verifier_state) =
            IOPVerificationGadget::<G, GG>::verifier_query_map_gadget(
                cs.ns(|| "verifier query set"),
                verifier_state,
            )?;

        let mut evaluation_keys = Vec::new();
        for (point_label, (_, poly_set)) in query_map.iter() {
            for poly_label in poly_set {
                evaluation_keys.push((poly_label.clone(), point_label.clone()));
            }
        }
        evaluation_keys.sort();

        let mut evaluations = Evaluations::new();
        for (key, eval) in evaluation_keys.into_iter().zip(proof.evaluations.iter()) {
            evaluations.insert(key, eval.clone());
        }

        IOPVerificationGadget::<G, GG>::verify_sumchecks(
            cs.ns(|| "verify sumchecks"),
            &evaluations,
            &verifier_state,
        )?;

        let commitments: Vec<_> = index_vk
            .iter()
            .chain(init_comms.iter())
            .chain(first_comms.iter())
            .chain(second_comms.iter())
            .chain(third_comms.iter())
            .cloned()
            .zip(IOP::<G::ScalarField>::polynomial_labels())
            .map(|(c, l)| LabeledCommitmentGadget::new(l, c))
            .collect();

        Ok((query_map, evaluations, commitments, fs_rng))
    }

    pub fn succinct_verify_opening<CS: ConstraintSystemAbstract<G::BaseField>>(
        mut cs: CS,
        pc_vk: &PC::VerifierKey,
        proof: &ProofGadget<G, PC, PCG>,
        labeled_comms: Vec<
            LabeledCommitmentGadget<G::BaseField, PC::Commitment, PCG::CommitmentGadget>,
        >,
        query_map: QueryMap<NonNativeFieldGadget<G::ScalarField, G::BaseField>>,
        evaluations: Evaluations<NonNativeFieldGadget<G::ScalarField, G::BaseField>>,
        fs_rng: &mut PCG::RandomOracleGadget,
    ) -> Result<(), SynthesisError> {
        fs_rng.enforce_record(
            cs.ns(|| "enforce absorb evaluations"),
            proof.evaluations.as_slice(),
        )?;

        PCG::succinct_verify_multi_poly_multi_point(
            cs.ns(|| "succinct opening proof check"),
            &pc_vk,
            &labeled_comms,
            &query_map,
            &evaluations,
            &proof.pc_proof,
            fs_rng,
        )
        .map_err(|err| SynthesisError::Other(err.to_string()))?;

        Ok(())
    }

    pub fn succinct_verify<CS: ConstraintSystemAbstract<G::BaseField>>(
        mut cs: CS,
        pc_vk: &PC::VerifierKey,
        index_vk: &VerifierKeyGadget<G, PC, PCG>,
        public_input: &[NonNativeFieldGadget<G::ScalarField, G::BaseField>],
        proof: &ProofGadget<G, PC, PCG>,
    ) -> Result<(), SynthesisError> {
        let (query_map, evaluations, labeled_commitments, mut fs_rng) =
            Self::verify_iop(cs.ns(|| "verify IOP"), pc_vk, index_vk, public_input, proof)?;

        Self::succinct_verify_opening(
            cs.ns(|| "succinct verify opening proof"),
            pc_vk,
            proof,
            labeled_commitments,
            query_map,
            evaluations,
            &mut fs_rng,
        )?;

        Ok(())
    }

    fn compute_commit_from_lagrange_representation<CS: ConstraintSystemAbstract<G::BaseField>>(
        mut cs: CS,
        lagrange_poly_comms: &[PC::Commitment],
        poly_evals: &[NonNativeFieldGadget<G::ScalarField, G::BaseField>],
    ) -> Result<PCG::CommitmentGadget, SynthesisError> {
        assert!(poly_evals.len() <= lagrange_poly_comms.len());

        // Get the bits from the non native field gadget
        let poly_evals_bits = poly_evals
            .iter()
            .enumerate()
            .map(|(i, poly_coord)| {
                //TODO: Is range proof really needed here ?
                let mut bits = poly_coord
                    .to_bits_strict(cs.ns(|| format!("poly coord {} to bits strict", i)))?;
                bits.reverse();
                Ok(bits)
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        let result = PCG::CommitmentGadget::fixed_base_msm(
            cs.ns(|| "fixed base msm between lagrange comms and public inputs"),
            lagrange_poly_comms.iter(),
            poly_evals_bits.iter(),
        )?;

        Ok(result)
    }
}
