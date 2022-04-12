use algebra::ToConstraintField;
use fiat_shamir::FiatShamirRng;
use poly_commit::{ipa_pc::{IPACurve, VerifierKey as DLogVerifierKey}, DomainExtendedPolynomialCommitment, PolynomialCommitment};
use marlin::{VerifierKey as MarlinVerifierKey, Marlin};
use crate::darlin::{pcd::{simple_marlin::MarlinProof, PCD, error::PCDError}, accumulators::{dlog::{DualDLogItemAccumulator, DualDLogItem}, ItemAccumulator}};

use super::*;

pub struct Merge1PCD<'a, G1, G2, FS: 'static + FiatShamirRng>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
{
    pub proof: MarlinProof<G1, FS>,
    pub accs: DualDLogItem<G1, G2>,
    pub usr_ins: Vec<G1::ScalarField>,
    pub lifetime: PhantomData<&'a ()>
}

pub struct Merge1PCDVerifierKey<'a, G1, G2, FS: 'static + FiatShamirRng>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    FS: FiatShamirRng + 'static
{
    pub marlin_vk: &'a MarlinVerifierKey<G1, DomainExtendedIpaPc<G1, FS>>,
    pub dlog_vks: (&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>),
}

impl<'a, G1, G2, FS> AsRef<(&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>)> for Merge1PCDVerifierKey<'a, G1, G2, FS>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    FS: FiatShamirRng + 'static
{
    fn as_ref(&self) -> &(&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>) {
        &self.dlog_vks
    }
}

impl<'a, G1, G2, FS> PCD for Merge1PCD<'a, G1, G2, FS>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    FS: 'static + FiatShamirRng
{
    type PCDAccumulator = DualDLogItemAccumulator<'a, G1, G2, FS>;
    type PCDVerifierKey = Merge1PCDVerifierKey<'a, G1, G2, FS>;

    fn succinct_verify(
        &self,
        vk: &Self::PCDVerifierKey,
    ) -> Result<<Self::PCDAccumulator as ItemAccumulator>::Item, PCDError> 
    {
        // Get "system inputs"
        let mut public_inputs = self.accs.to_field_elements().map_err(|_| {
            PCDError::FailedSuccinctVerification(
                "Unable to convert accumulators to native field elements".to_owned(),
            )
        })?;

        // Append user inputs
        public_inputs.extend_from_slice(self.usr_ins.as_slice());

        // Verify AHP
        let (query_map, evaluations, labeled_comms, mut fs_rng) = Marlin::<G1, DomainExtendedIpaPc<G1, FS>>::verify_iop(
            vk.dlog_vks.0,
            vk.marlin_vk,
            public_inputs.as_slice(),
            &self.proof,
        ).map_err(|e| {
            PCDError::FailedSuccinctVerification(format!("{:?}", e))
        })?;

        // record evaluations and sample new challenge
        fs_rng
            .record(self.proof.evaluations.clone())
            .map_err(|e| {
                PCDError::FailedSuccinctVerification(format!("{:?}", e))
            })?;

        // Succinct verify DLOG proof
        let verifier_state = DomainExtendedPolynomialCommitment::<G1, InnerProductArgPC::<G1, FS>>::succinct_multi_point_multi_poly_verify(
            vk.dlog_vks.0,
            &labeled_comms,
            &query_map,
            &evaluations,
            &self.proof.pc_proof,
            &mut fs_rng,
        ).map_err(|e| {
            PCDError::FailedSuccinctVerification(e.to_string())
        })?;

        if verifier_state.is_none() {
            Err(PCDError::FailedSuccinctVerification(
                "Succinct verify failed".to_owned(),
            ))?
        }

        // Verification successfull: return new accumulator
        let acc = verifier_state.unwrap();
        let mut new_acc = self.accs.clone();
        new_acc.0.push(acc);

        Ok(new_acc)
    }

    fn get_id() -> String {
        "Merge1PCD".to_string()
    }
} 