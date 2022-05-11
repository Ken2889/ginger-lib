//! Final Darlin proof carrying data. The final Darlin is the last node of the
//! exiting/conversion chain of our Darlin PCD scheme, and provides a (coboundary)
//! Marlin proof plus the dlog accumulators of the previous and pre-previous node.
use crate::darlin::accumulators::dlog::DualDLogItem;
use crate::darlin::{
    accumulators::dlog::DualDLogAccumulator,
    accumulators::Accumulator,
    data_structures::*,
    pcd::{error::PCDError, PCD},
    DomainExtendedIpaPc, FinalDarlin, FinalDarlinVerifierKey,
};
use algebra::{DualCycle, EndoMulCurve};
use bench_utils::*;
use derivative::Derivative;
use fiat_shamir::FiatShamirRng;
use poly_commit::{
    ipa_pc::{InnerProductArgPC, VerifierKey as DLogVerifierKey},
    DomainExtendedPolynomialCommitment, PolynomialCommitment,
};
use std::marker::PhantomData;

/// As every PCD, the `FinalDarlinPCD` comes as a proof plus "statement".
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct FinalDarlinPCD<'a, G1: EndoMulCurve, G2: EndoMulCurve, FS: FiatShamirRng + 'static> {
    /// A `FinalDarlinProof` is a Marlin proof plus deferred dlog accumulators
    pub final_darlin_proof: FinalDarlinProof<G1, G2, FS>,
    /// The user inputs form essentially the "statement" of the recursive proof.
    pub usr_ins: Vec<G1::ScalarField>,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a, G1, G2, FS> FinalDarlinPCD<'a, G1, G2, FS>
where
    G1: EndoMulCurve,
    G2: EndoMulCurve,
    G1: DualCycle<G2>,
    FS: FiatShamirRng + 'static,
{
    pub fn new(
        final_darlin_proof: FinalDarlinProof<G1, G2, FS>,
        usr_ins: Vec<G1::ScalarField>,
    ) -> Self {
        Self {
            final_darlin_proof,
            usr_ins,
            _lifetime: PhantomData,
        }
    }
}

/// To verify the PCD of a final Darlin we only need the `FinalDarlinVerifierKey` (or, the
/// IOP verifier key) of the final circuit and the two dlog committer keys for G1 and G2.
pub struct FinalDarlinPCDVerifierKey<
    'a,
    G1: EndoMulCurve,
    G2: EndoMulCurve,
    FS: FiatShamirRng + 'static,
> {
    pub final_darlin_vk: &'a FinalDarlinVerifierKey<G1, DomainExtendedIpaPc<G1, FS>>,
    pub dlog_vks: (&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>),
}

impl<'a, G1: EndoMulCurve, G2: EndoMulCurve, FS: FiatShamirRng + 'static>
    AsRef<(&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>)>
    for FinalDarlinPCDVerifierKey<'a, G1, G2, FS>
{
    fn as_ref(&self) -> &(&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>) {
        &self.dlog_vks
    }
}

impl<'a, G1, G2, FS> PCD for FinalDarlinPCD<'a, G1, G2, FS>
where
    G1: EndoMulCurve,
    G2: EndoMulCurve,
    G1: DualCycle<G2>,
    FS: FiatShamirRng + 'static,
{
    type PCDAccumulator = DualDLogAccumulator<'a, G1, G2, FS>;
    type PCDVerifierKey = FinalDarlinPCDVerifierKey<'a, G1, G2, FS>;

    fn succinct_verify(
        &self,
        vk: &Self::PCDVerifierKey,
    ) -> Result<<Self::PCDAccumulator as Accumulator>::Item, PCDError> {
        let succinct_time = start_timer!(|| "Finalized Darlin succinct verifier");

        let ahp_verify_time = start_timer!(|| "AHP verify");

        // Verify sumchecks
        let (query_map, evaluations, labeled_comms, mut fs_rng) =
            FinalDarlin::<G1, G2, FS>::verify_ahp(
                vk.dlog_vks.0,
                vk.final_darlin_vk,
                self.usr_ins.as_slice(),
                &self.final_darlin_proof,
            )
            .map_err(|e| {
                end_timer!(ahp_verify_time);
                end_timer!(succinct_time);
                PCDError::FailedSuccinctVerification(format!("{:?}", e))
            })?;

        end_timer!(ahp_verify_time);

        // record evaluations and sample new challenge
        fs_rng
            .record(self.final_darlin_proof.proof.evaluations.clone())
            .map_err(|e| {
                end_timer!(succinct_time);
                PCDError::FailedSuccinctVerification(format!("{:?}", e))
            })?;

        let pc_verify_time = start_timer!(|| "PC succinct verify");

        // Succinct verify DLOG proof
        let verifier_state = DomainExtendedPolynomialCommitment::<G1, InnerProductArgPC::<G1, FS>>::succinct_multi_point_multi_poly_verify(
            vk.dlog_vks.0,
            &labeled_comms,
            &query_map,
            &evaluations,
            &self.final_darlin_proof.proof.pc_proof,
            &mut fs_rng,
        ).map_err(|e| {
            end_timer!(pc_verify_time);
            end_timer!(succinct_time);
            PCDError::FailedSuccinctVerification(e.to_string())
        })?;

        end_timer!(pc_verify_time);

        if verifier_state.is_none() {
            end_timer!(succinct_time);
            Err(PCDError::FailedSuccinctVerification(
                "Succinct verify failed".to_owned(),
            ))?
        }

        // Verification successfull: return new accumulator
        let acc = verifier_state.unwrap();

        end_timer!(succinct_time);
        Ok(DualDLogItem {
            native: vec![
                acc,
                self.final_darlin_proof.deferred.pre_previous_acc.clone(),
            ],
            non_native: vec![self.final_darlin_proof.deferred.previous_acc.clone()],
        })
    }
}
