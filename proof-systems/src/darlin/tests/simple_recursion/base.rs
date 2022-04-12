use algebra::{Group, ToConstraintField};
use fiat_shamir::FiatShamirRng;
use marlin::{ProverKey, VerifierKey, Marlin};
use poly_commit::ipa_pc::{CommitterKey, IPACurve};
use primitives::{PoseidonParameters, SBox};
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};
use r1cs_crypto::SBoxGadget;
use r1cs_std::{fields::fp::FpGadget, alloc::AllocGadget, eq::EqGadget};
use crate::darlin::{DomainExtendedIpaPc, pcd::simple_marlin::MarlinProof, accumulators::dlog::DualDLogItem};
use digest::Digest;
use super::{HashChainTransitionGadget, StateTransitionGadget, merge::Merge1PCD};
use std::marker::PhantomData;

/// Very simple test circuit that enforces H(start, incremental) == end
pub struct TestBaseCircuit<
    G1: IPACurve,
    P: PoseidonParameters<Fr = G1::ScalarField>,
    SB: SBox<Field = G1::ScalarField, Parameters = P>,
    SBG: SBoxGadget<G1::ScalarField, SB>,
> {
    start: Option<G1::ScalarField>,
    incremental: Option<G1::ScalarField>,
    end: Option<G1::ScalarField>,
    _hash_params: PhantomData<P>,
    _sbox: PhantomData<SB>,
    _sbox_gadget: PhantomData<SBG>
}

impl<G1, P, SB, SBG> ConstraintSynthesizer<G1::ScalarField> for TestBaseCircuit<G1, P, SB, SBG>
where
    G1: IPACurve,
    P: PoseidonParameters<Fr = G1::ScalarField>,
    SB: SBox<Field = G1::ScalarField, Parameters = P>,
    SBG: SBoxGadget<G1::ScalarField, SB>,
{
    fn generate_constraints<CS: ConstraintSystemAbstract<G1::ScalarField>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> 
    {
        // Allocate data
        let start_g = FpGadget::<G1::ScalarField>::alloc_input(
            cs.ns(|| "alloc input start"),
            || self.start.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let incremental_g = FpGadget::<G1::ScalarField>::alloc(
            cs.ns(|| "alloc input incremental"),
            || self.incremental.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let expected_end_g = FpGadget::<G1::ScalarField>::alloc_input(
            cs.ns(|| "alloc input end"),
            || self.end.ok_or(SynthesisError::AssignmentMissing)
        )?;

        // Enforce state transition
        let hash_chain_transition_gadget = HashChainTransitionGadget::<G1::ScalarField, P, SB, SBG>::new(incremental_g);
        let actual_end_g = hash_chain_transition_gadget.enforce_state_transition(
            cs.ns(|| "enforce state transition"),
            start_g
        )?;

        // Check that state transition led to expected state
        expected_end_g.enforce_equal(cs.ns(|| "check state transition"), &actual_end_g)?;

        Ok(())
    }
}

pub(crate) fn setup<
    G1: IPACurve,
    P: PoseidonParameters<Fr = G1::ScalarField>,
    SB: SBox<Field = G1::ScalarField, Parameters = P>,
    SBG: SBoxGadget<G1::ScalarField, SB>,
    FS: FiatShamirRng,
    D: Digest
>(ck: &CommitterKey<G1>) -> (ProverKey<G1, DomainExtendedIpaPc<G1, FS>>, VerifierKey<G1, DomainExtendedIpaPc<G1, FS>>)
{
    let c = TestBaseCircuit::<G1, P, SB, SBG> {
        start: None,
        incremental: None,
        end: None,
        _hash_params: PhantomData,
        _sbox: PhantomData,
        _sbox_gadget: PhantomData,
    };

    Marlin::<G1, DomainExtendedIpaPc<G1, FS>>::circuit_specific_setup::<_, D>(ck, c).unwrap()
}

pub(crate) fn get_pcd<
    'a,
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    P: PoseidonParameters<Fr = G1::ScalarField>,
    SB: SBox<Field = G1::ScalarField, Parameters = P>,
    SBG: SBoxGadget<G1::ScalarField, SB>,
    FS: FiatShamirRng,
    D: Digest
>(
    ck: &CommitterKey<G1>,
    pk: &ProverKey<G1, DomainExtendedIpaPc<G1, FS>>,
    start: G1::ScalarField,
    incremental: G1::ScalarField,
    end: G1::ScalarField,
) -> Merge1PCD<'a, G1, G2, FS>
{
    let c = TestBaseCircuit::<G1, P, SB, SBG> {
        start: Some(start),
        incremental: Some(incremental),
        end: Some(end),
        _hash_params: PhantomData,
        _sbox: PhantomData,
        _sbox_gadget: PhantomData,
    };

    let proof = Marlin::<G1, DomainExtendedIpaPc<G1, FS>>::prove(pk, ck, c, false, None).unwrap();

    Merge1PCD::<G1, G2, FS> {
        proof: MarlinProof(proof),
        accs: DualDLogItem::<G1, G2>(vec![], vec![]),
        usr_ins: vec![start, incremental],
        lifetime: PhantomData,
    }
}