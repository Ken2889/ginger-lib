//! The proof data struct (and its components) of a final Darlin, i.e. last node of
//! our conversion/exiting chain.
use crate::darlin::{accumulators::dlog::{DLogItem, DualDLogItem}, pcd::simple_marlin::{MarlinProof, MarlinVerifierKey}};
use algebra::{
    serialize::*, Group, SemanticallyValid, ToConstraintField,
    UniformRand,
};
use fiat_shamir::FiatShamirRng;
use poly_commit::ipa_pc::{
    CommitterKey as DLogCommitterKey, InnerProductArgPC, SuccinctCheckPolynomial, IPACurve,
};
use derivative::Derivative;
use marlin::ProverKey as MarlinProverKey;
use rand::RngCore;

/// The `FinalDarlinDeferredData`, assuming that the final node is in G1.
/// This node serves an ordinary Marlin proof plus the dlog accumulators
/// passed from the previous two nodes of the conversion chain.
/// Note: Later the struct could include more elements as we might want to defer
/// addional algebraic checks over G1::BaseField.
#[derive(Default, Clone, Debug, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct FinalDarlinDeferredData<G1: IPACurve, G2: IPACurve> {
    // the dlog accumulator from the previous node, a Rainbow-Marlin node in G2
    pub(crate) previous_acc: DLogItem<G2>,
    // the dlog accumulator from the pre-previous node, a Rainbow-Marlin node in G1
    pub(crate) pre_previous_acc: DLogItem<G1>,
}

impl<G1: IPACurve, G2: IPACurve> SemanticallyValid for FinalDarlinDeferredData<G1, G2> {
    fn is_valid(&self) -> bool {
        self.previous_acc.is_valid() && self.pre_previous_acc.is_valid()
    }
}

impl<G1, G2> FinalDarlinDeferredData<G1, G2>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
{
    // generates random FinalDarlinDeferredData, for test purposes only.
    pub fn generate_random<R: RngCore, FS: FiatShamirRng>(
        rng: &mut R,
        committer_key_g1: &DLogCommitterKey<G1>,
        committer_key_g2: &DLogCommitterKey<G2>,
    ) -> Self {
        // Generate valid accumulator over G1 starting from random check_poly
        let log_key_len_g1 = algebra::log2(committer_key_g1.comm_key.len());
        let random_check_poly_g1 = SuccinctCheckPolynomial::<G1>::from_chals(
            (0..log_key_len_g1 as usize)
                .map(|_| u128::rand(rng).into())
                .collect(),
        );
        let final_comm_key_g1 = InnerProductArgPC::<G1, FS>::inner_commit(
            committer_key_g1.comm_key.as_slice(),
            random_check_poly_g1.compute_coeffs().as_slice(),
            None,
            None,
        )
        .unwrap();

        let acc_g1 = DLogItem::<G1> {
            final_comm_key: final_comm_key_g1,
            check_poly: random_check_poly_g1,
        };

        // Generate valid accumulator over G2 starting from random check_poly
        let log_key_len_g2 = algebra::log2(committer_key_g2.comm_key.len());
        let random_check_poly_g2 = SuccinctCheckPolynomial::<G2>::from_chals(
            (0..log_key_len_g2 as usize)
                .map(|_| u128::rand(rng).into())
                .collect(),
        );

        let final_comm_key_g2 = InnerProductArgPC::<G2, FS>::inner_commit(
            committer_key_g2.comm_key.as_slice(),
            random_check_poly_g2.compute_coeffs().as_slice(),
            None,
            None,
        )
        .unwrap();

        let acc_g2 = DLogItem::<G2> {
            final_comm_key: final_comm_key_g2,
            check_poly: random_check_poly_g2,
        };

        // Return accumulators in deferred struct
        Self {
            previous_acc: acc_g2,
            pre_previous_acc: acc_g1,
        }
    }
}

impl<G1, G2> ToConstraintField<G1::ScalarField> for FinalDarlinDeferredData<G1, G2>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
{
    /// Conversion of the MarlinDeferredData to circuit inputs, which are elements
    /// over G1::ScalarField.
    fn to_field_elements(&self) -> Result<Vec<G1::ScalarField>, Box<dyn std::error::Error>> {
        DualDLogItem::<G1, G2>(vec![self.pre_previous_acc.clone()], vec![self.previous_acc.clone()])
            .to_field_elements()
    }
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
/// A FinalDarlinProof has two dlog accumulators, one from the previous, and on from the
/// pre-previous node of the conversion chain.
pub struct FinalDarlinProof<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> {
    /// Full Marlin proof without deferred arithmetics in G1.
    pub proof: MarlinProof<G1, FS>,
    /// Deferred accumulators
    pub deferred: FinalDarlinDeferredData<G1, G2>,
}

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> SemanticallyValid
    for FinalDarlinProof<G1, G2, FS>
{
    fn is_valid(&self) -> bool {
        self.proof.is_valid() && self.deferred.is_valid()
    }
}

pub type FinalDarlinProverKey<G, PC> = MarlinProverKey<G, PC>;
pub type FinalDarlinVerifierKey<G, FS> = MarlinVerifierKey<G, FS>;