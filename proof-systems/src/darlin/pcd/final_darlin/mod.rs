//! Final Darlin proof carrying data. The final Darlin is the last node of the
//! exiting/conversion chain of our Darlin PCD scheme, and provides a (coboundary)
//! Marlin proof plus the dlog accumulators of the previous and pre-previous node.
use crate::darlin::{
    accumulators::dlog::{DualDLogItem, DualDLogItemAccumulator},
    accumulators::ItemAccumulator,
    pcd::{error::PCDError, PCD}, DomainExtendedIpaPc,
};
use algebra::{Group, ToConstraintField};
use bench_utils::*;
use fiat_shamir::FiatShamirRng;
use poly_commit::{
    ipa_pc::{InnerProductArgPC, VerifierKey as DLogVerifierKey, IPACurve},
    DomainExtendedPolynomialCommitment, PolynomialCommitment,
};
use derivative::Derivative;
use marlin::Marlin;
use std::marker::PhantomData;

pub mod data_structures;
pub use data_structures::*;

const FINAL_DARLIN_PCD_IDENTIFIER: &str = "FinalDarlin";

/// As every PCD, the `FinalDarlinPCD` comes as a proof plus "statement".
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct FinalDarlinPCD<'a, G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> {
    /// A `FinalDarlinProof` is a Marlin proof plus deferred dlog accumulators
    pub final_darlin_proof: FinalDarlinProof<G1, G2, FS>,
    /// The user inputs form essentially the "statement" of the recursive proof.
    pub usr_ins: Vec<G1::ScalarField>,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a, G1, G2, FS> FinalDarlinPCD<'a, G1, G2, FS>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
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
    G1: IPACurve,
    G2: IPACurve,
    FS: FiatShamirRng + 'static,
> {
    pub final_darlin_vk: &'a FinalDarlinVerifierKey<
        G1,
        DomainExtendedIpaPc<G1, FS>,
    >,
    pub dlog_vks: (&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>),
}

impl<'a, G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static>
    AsRef<(&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>)>
    for FinalDarlinPCDVerifierKey<'a, G1, G2, FS>
{
    fn as_ref(&self) -> &(&'a DLogVerifierKey<G1>, &'a DLogVerifierKey<G2>) {
        &self.dlog_vks
    }
}

impl<'a, G1, G2, FS> PCD for FinalDarlinPCD<'a, G1, G2, FS>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    FS: FiatShamirRng + 'static,
{
    type PCDAccumulator = DualDLogItemAccumulator<'a, G1, G2, FS>;
    type PCDVerifierKey = FinalDarlinPCDVerifierKey<'a, G1, G2, FS>;

    fn succinct_verify(
        &self,
        vk: &Self::PCDVerifierKey,
    ) -> Result<<Self::PCDAccumulator as ItemAccumulator>::Item, PCDError> {
        let succinct_time = start_timer!(|| "Finalized Darlin succinct verifier");

        let iop_verify_time = start_timer!(|| "IOP verify");

        // Get "system inputs"
        let mut public_inputs = self.final_darlin_proof.deferred.to_field_elements().map_err(|_| {
            PCDError::FailedSuccinctVerification(
                "Unable to convert proof.deferred to native field elements".to_owned(),
            )
        })?;

        // Append user inputs
        public_inputs.extend_from_slice(self.usr_ins.as_slice());

        // Verify AHP
        let (query_map, evaluations, labeled_comms, mut fs_rng) = Marlin::<G1, DomainExtendedIpaPc<G1, FS>>::verify_iop(
            vk.dlog_vks.0,
            vk.final_darlin_vk,
            public_inputs.as_slice(),
            &self.final_darlin_proof.proof,
        ).map_err(|e| {
            end_timer!(iop_verify_time);
            end_timer!(succinct_time);
            PCDError::FailedSuccinctVerification(format!("{:?}", e))
        })?;

        end_timer!(iop_verify_time);

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
        Ok(DualDLogItem::<G1, G2>(
            vec![
                acc,
                self.final_darlin_proof.deferred.pre_previous_acc.clone(),
            ],
            vec![self.final_darlin_proof.deferred.previous_acc.clone()],
        ))
    }

    fn get_id() -> String {
        FINAL_DARLIN_PCD_IDENTIFIER.to_string()
    }
}


// TODO: The way we refactoed the traits, for the moment, doesn't allow to implement PCDNode for FinalDarlin.
//       We can do it only when we have RainbowMarlin and the PCDCircuit to verify it.
//

// // A final Darlin in G1, and the previous node in G2.
// pub struct FinalDarlinNode<'a, G1: EndoMulCurve, G2: EndoMulCurve, FS: FiatShamirRng + 'static>(
//     #[doc(hidden)] PhantomData<G1>,
//     #[doc(hidden)] PhantomData<G2>,
//     #[doc(hidden)] PhantomData<FS>,
//     #[doc(hidden)] PhantomData<&'a ()>,
// );

// impl<'a, G1, G2, FS> PCDNode<G1, G2> for FinalDarlinNode<'a, G1, G2, FS>
// where
//     G1: EndoMulCurve<BaseField = <G2 as Group>::ScalarField>
//         + ToConstraintField<<G2 as Group>::ScalarField>,
//     G2: EndoMulCurve<BaseField = <G1 as Group>::ScalarField>
//         + ToConstraintField<<G1 as Group>::ScalarField>,
//     FS: FiatShamirRng + 'static,
// {
//     type ProverKey = FinalDarlinProverKey<
//         G1,
//         DomainExtendedIpaPc<G1, FS>,
//     >;
//     type VerifierKey = FinalDarlinVerifierKey<
//         G1,
//         DomainExtendedIpaPc<G1, FS>,
//     >;
//     type OutputPCD = FinalDarlinPCD<'a, G1, G2, FS>;

//     /// Generate the index-specific (i.e., circuit-specific) prover and verifier
//     /// keys from the dedicated PCDCircuit.
//     /// This is a deterministic algorithm that anyone can rerun.
//     fn index<C: PCDCircuit<G1>, D: Digest>(
//         committer_key: &DLogProverKey<G1>,
//         config: C::SetupData,
//     ) -> Result<
//         (
//             FinalDarlinProverKey<
//                 G1,
//                 DomainExtendedIpaPc<G1, FS>,
//             >,
//             FinalDarlinVerifierKey<
//                 G1,
//                 DomainExtendedIpaPc<G1, FS>,
//             >,
//         ),
//         PCDError,
//     > {
//         let c = C::init(config);
//         let res = Marlin::<G1, DomainExtendedIpaPc<G1, FS>>::circuit_specific_setup::<_, D>(committer_key, c)?;

//         Ok(res)
//     }

//     /// Create and return a FinalDarlinPCD, given previous PCDs and a PCDCircuit
//     /// that (partially) verify them along with some additional data.
//     fn prove<C>(
//         index_pk: &FinalDarlinProverKey<
//             G1,
//             DomainExtendedIpaPc<G1, FS>,
//         >,
//         pc_pk: &DLogProverKey<G1>,
//         config: C::SetupData,
//         // In future, this will be explicitly a RainbowDarlinPCD
//         previous: Vec<C::PreviousPCD>,
//         previous_vks: Vec<<C::PreviousPCD as PCD>::PCDVerifierKey>,
//         additional_data: C::AdditionalData,
//         zk: bool,
//         zk_rng: Option<&mut dyn RngCore>,
//     ) -> Result<FinalDarlinPCD<'a, G1, G2, FS>, PCDError>
//     where
//         C: PCDCircuit<G1, SystemInputs = FinalDarlinDeferredData<G1, G2>>,
//     {
//         // init the recursive circuit using the previous PCDs and the additional data.
//         let c = C::init_state(config, previous, previous_vks, additional_data);

//         // get the system and user inputs from the recursive circuit
//         let sys_ins = c.get_sys_ins()?.clone();

//         let usr_ins = c.get_usr_ins()?;

//         // run the Marlin prover on the initialized recursive circuit
//         let proof =
//             Marlin::<G1, DomainExtendedIpaPc<G1, FS>>::prove(
//                 index_pk, pc_pk, c, zk, zk_rng,
//             )?;

//         let proof = FinalDarlinProof::<G1, G2, FS> {
//             proof: MarlinProof(proof),
//             deferred: sys_ins,
//         };

//         Ok(FinalDarlinPCD::<G1, G2, FS>::new(proof, usr_ins))
//     }
// }
