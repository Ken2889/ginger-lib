//! Simple Marlin "proof carrying data". This corresponds to non-recursive applications.
use crate::darlin::{
    accumulators::{
        dlog::{DLogItem, DLogItemAccumulator},
        ItemAccumulator,
    },
    pcd::{error::PCDError, PCD},
};
use algebra::{serialize::*, Curve, SemanticallyValid};
use digest::Digest;
use marlin::{Marlin, Proof, VerifierKey as MarlinVerifierKey, IOP};
use poly_commit::{
    fiat_shamir_rng::FiatShamirRng,
    ipa_pc::{InnerProductArgPC, VerifierKey as DLogVerifierKey},
    DomainExtendedPolynomialCommitment, PolynomialCommitment,
};
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
pub struct MarlinProof<G: Curve, D: Digest + 'static>(
    pub Proof<G, DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, D>>>,
);

impl<G: Curve, D: Digest> Deref for MarlinProof<G, D> {
    type Target = Proof<G, DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, D>>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<G: Curve, D: Digest> DerefMut for MarlinProof<G, D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<G: Curve, D: Digest> SemanticallyValid for MarlinProof<G, D> {
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

        self.commitments.is_valid() &&  // Check that each commitment is valid
            self.evaluations.len() == evaluations_num && // Check correct number of evaluations
            self.evaluations.is_valid() && // Check validity of each evaluation
            // Check opening proof
            self.pc_proof.is_valid()
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct SimpleMarlinPCD<'a, G: Curve, D: Digest + 'static> {
    pub proof: MarlinProof<G, D>,
    pub usr_ins: Vec<G::ScalarField>,
    _lifetime: PhantomData<&'a ()>,
}

/// As every PCD, the `SimpleMarlinPCD` comes as a proof plus "statement".
impl<'a, G, D> SimpleMarlinPCD<'a, G, D>
where
    G: Curve,
    D: Digest + 'a,
{
    pub fn new(
        // A normal (coboundary) Marlin proof
        proof: MarlinProof<G, D>,
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
pub struct SimpleMarlinPCDVerifierKey<'a, G: Curve, D: Digest + 'static>(
    pub &'a MarlinVerifierKey<G, DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, D>>>,
    pub &'a DLogVerifierKey<G>,
);

impl<'a, G: Curve, D: Digest> AsRef<DLogVerifierKey<G>> for SimpleMarlinPCDVerifierKey<'a, G, D> {
    fn as_ref(&self) -> &DLogVerifierKey<G> {
        &self.1
    }
}

impl<'a, G, D> PCD for SimpleMarlinPCD<'a, G, D>
where
    G: Curve,
    D: Digest + 'static,
{
    type PCDAccumulator = DLogItemAccumulator<G, D>;
    type PCDVerifierKey = SimpleMarlinPCDVerifierKey<'a, G, D>;

    fn succinct_verify(
        &self,
        vk: &Self::PCDVerifierKey,
    ) -> Result<<Self::PCDAccumulator as ItemAccumulator>::Item, PCDError> {
        let succinct_time = start_timer!(|| "Marlin succinct verifier");

        // Verify the IOP/AHP
        let (query_set, evaluations, labeled_comms, mut fs_rng) = Marlin::<
            G,
            DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, D>>,
            D,
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

        // Absorb evaluations and sample new challenge
        fs_rng.absorb(&self.proof.evaluations);

        // Succinct verify DLOG proof
        let verifier_state = DomainExtendedPolynomialCommitment::<G, InnerProductArgPC::<G, D>>::succinct_multi_point_multi_poly_verify(
            &vk.1,
            &labeled_comms,
            &query_set,
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

        let verifier_state = verifier_state.unwrap();

        // Successfull verification: return current accumulator
        let acc = DLogItem::<G> {
            g_final: verifier_state.final_comm_key.clone(),
            xi_s: verifier_state.check_poly.clone(),
        };

        end_timer!(succinct_time);
        Ok(acc)
    }
}
