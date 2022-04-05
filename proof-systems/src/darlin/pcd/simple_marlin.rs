//! Simple Marlin "proof carrying data". This corresponds to non-recursive applications.
use crate::darlin::{
    accumulators::{
        dlog::DLogItemAccumulator,
        ItemAccumulator,
    },
    pcd::{error::PCDError, PCD},
    DomainExtendedIpaPc,
};
use algebra::{serialize::*, SemanticallyValid};
use bench_utils::*;
use fiat_shamir::FiatShamirRng;
use marlin::{Marlin, Proof, VerifierKey as MarlinVerifierKey, IOP};
use poly_commit::{
    ipa_pc::{InnerProductArgPC, VerifierKey as DLogVerifierKey, IPACurve},
    DomainExtendedPolynomialCommitment, PolynomialCommitment,
};
use derivative::Derivative;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct MarlinProof<G: IPACurve, FS: FiatShamirRng + 'static>(
    pub Proof<G, DomainExtendedIpaPc<G, FS>>,
);

impl<G: IPACurve, FS: FiatShamirRng> Deref for MarlinProof<G, FS> {
    type Target = Proof<G, DomainExtendedIpaPc<G, FS>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<G: IPACurve, FS: FiatShamirRng> DerefMut for MarlinProof<G, FS> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<G: IPACurve, FS: FiatShamirRng> SemanticallyValid for MarlinProof<G, FS> {
    fn is_valid(&self) -> bool {
        // Check commitments number and validity
        let num_rounds = 3;
        let comms_per_round = vec![3, 2, 2];

        // Check commitments are grouped into correct num_rounds
        if self.commitments.len() != num_rounds {
            return false;
        };

        // Check that each round has the expected number of commitments
        for i in 0..comms_per_round.len() {
            if self.commitments[i].len() != comms_per_round[i] {
                return false;
            };
        }

        // Check evaluations num
        let num_polys = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len()
            + IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len();
        let evaluations_num = num_polys + 2;
        #[cfg(feature = "circuit-friendly")]
        let evaluations_num = evaluations_num + 1; // Vanishing poly v_h is evaluated at two points.

        self.commitments.is_valid() &&  // Check that each commitment is valid
            self.evaluations.len() == evaluations_num && // Check correct number of evaluations
            self.evaluations.is_valid() && // Check validity of each evaluation
            // Check opening proof
            self.pc_proof.is_valid()
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct SimpleMarlinPCD<'a, G: IPACurve, FS: FiatShamirRng + 'static> {
    pub proof: MarlinProof<G, FS>,
    pub usr_ins: Vec<G::ScalarField>,
    _lifetime: PhantomData<&'a ()>,
}

/// As every PCD, the `SimpleMarlinPCD` comes as a proof plus "statement".
impl<'a, G, FS> SimpleMarlinPCD<'a, G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng + 'a,
{
    pub fn new(
        // A normal (coboundary) Marlin proof
        proof: MarlinProof<G, FS>,
        // The "statement" of the proof. Typically the full public inputs
        usr_ins: Vec<G::ScalarField>,
    ) -> Self {
        Self {
            proof,
            usr_ins,
            _lifetime: PhantomData,
        }
    }
}

/// To verify the PCD of a simple Marlin we only need the `MarlinVerifierKey` (or, the
/// IOP verifier key) of the circuit, and the two dlog committer keys for G1 and G2.
pub struct SimpleMarlinPCDVerifierKey<'a, G: IPACurve, FS: FiatShamirRng + 'static>(
    pub &'a MarlinVerifierKey<G, DomainExtendedIpaPc<G, FS>>,
    pub &'a DLogVerifierKey<G>,
);

impl<'a, G: IPACurve, FS: FiatShamirRng> AsRef<DLogVerifierKey<G>>
    for SimpleMarlinPCDVerifierKey<'a, G, FS>
{
    fn as_ref(&self) -> &DLogVerifierKey<G> {
        &self.1
    }
}

impl<'a, G, FS> PCD for SimpleMarlinPCD<'a, G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng + 'static,
{
    type PCDAccumulator = DLogItemAccumulator<G, FS>;
    type PCDVerifierKey = SimpleMarlinPCDVerifierKey<'a, G, FS>;

    fn succinct_verify(
        &self,
        vk: &Self::PCDVerifierKey,
    ) -> Result<<Self::PCDAccumulator as ItemAccumulator>::Item, PCDError> {
        let succinct_time = start_timer!(|| "Marlin succinct verifier");

        // Verify the IOP/AHP
        let (query_map, evaluations, labeled_comms, mut fs_rng) = Marlin::<
            G,
            DomainExtendedIpaPc<G, FS>,
        >::verify_iop(
            &vk.1,
            &vk.0,
            self.usr_ins.as_slice(),
            &self.proof,
        )
        .map_err(|e| {
            end_timer!(succinct_time);
            PCDError::FailedSuccinctVerification(format!("{:?}", e))
        })?;

        // record evaluations and sample new challenge
        fs_rng.record(self.proof.evaluations.clone()).map_err(|e| {
            end_timer!(succinct_time);
            PCDError::FailedSuccinctVerification(format!("{:?}", e))
        })?;

        // Succinct verify DLOG proof
        let verifier_state = DomainExtendedPolynomialCommitment::<G, InnerProductArgPC::<G, FS>>::succinct_multi_point_multi_poly_verify(
            &vk.1,
            &labeled_comms,
            &query_map,
            &evaluations,
            &self.proof.pc_proof,
            &mut fs_rng,
        ).map_err(|e| {
            end_timer!(succinct_time);
            PCDError::FailedSuccinctVerification(e.to_string())
        })?;

        if verifier_state.is_none() {
            end_timer!(succinct_time);
            Err(PCDError::FailedSuccinctVerification(
                "Succinct verify failed".to_owned(),
            ))?
        }

        // Successfull verification: return current accumulator
        let acc = verifier_state.unwrap();

        end_timer!(succinct_time);
        Ok(acc)
    }
}
