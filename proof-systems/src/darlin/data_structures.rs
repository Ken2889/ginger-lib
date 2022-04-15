//! The proof data struct (and its components) of a final Darlin, i.e. last node of
//! our conversion/exiting chain.
use crate::darlin::pcd::simple_marlin::MarlinProof;
use algebra::{
    serialize::*, DualCycle, Group, PrimeField, SemanticallyValid, ToBits, ToConstraintField,
};
use derivative::Derivative;
use fiat_shamir::FiatShamirRng;
use poly_commit::ipa_pc::{CommitterKey as DLogCommitterKey, DLogItem, IPACurve};
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
    G1: IPACurve + ToConstraintField<<G1 as Group>::BaseField>,
    G2: IPACurve + ToConstraintField<<G2 as Group>::BaseField>,
    G1: DualCycle<G2>,
{
    // generates random FinalDarlinDeferredData, for test purposes only.
    pub fn generate_random<R: RngCore, FS: FiatShamirRng>(
        rng: &mut R,
        committer_key_g1: &DLogCommitterKey<G1>,
        committer_key_g2: &DLogCommitterKey<G2>,
    ) -> Self {
        Self {
            previous_acc: DLogItem::generate_random::<_, FS>(rng, committer_key_g2),
            pre_previous_acc: DLogItem::generate_random::<_, FS>(rng, committer_key_g1),
        }
    }
}

impl<G1, G2> ToConstraintField<G1::ScalarField> for FinalDarlinDeferredData<G1, G2>
where
    G1: IPACurve + ToConstraintField<<G1 as Group>::BaseField>,
    G2: IPACurve + ToConstraintField<<G2 as Group>::BaseField>,
    G1: DualCycle<G2>,
{
    /// Conversion of the MarlinDeferredData to circuit inputs, which are elements
    /// over G1::ScalarField.
    fn to_field_elements(&self) -> Result<Vec<G1::ScalarField>, Box<dyn std::error::Error>> {
        let to_skip = <G1::ScalarField as PrimeField>::size_in_bits() - 128;
        let mut fes = Vec::new();

        // Convert previous_acc into G1::ScalarField field elements (the circuit field,
        // called native in the sequel)

        // The final_comm_key of the previous node consists of native field elements only
        let final_comm_key_g2 = self.previous_acc.final_comm_key.clone();
        fes.append(&mut final_comm_key_g2.to_field_elements()?);

        // Convert check_poly, which are 128 bit elements from G2::ScalarField, to the native field.
        // We packing the full bit vector into native field elements as efficient as possible (yet
        // still secure).
        let mut check_poly_bits = Vec::new();
        for fe in self.previous_acc.check_poly.chals.iter() {
            let bits = fe.write_bits();
            // write_bits() outputs a Big Endian bit order representation of fe and the same
            // expects [bool].to_field_elements(): therefore we need to take the last 128 bits,
            // e.g. we need to skip the first MODULUS_BITS - 128 bits.
            debug_assert!(
                <[bool] as ToConstraintField<G2::ScalarField>>::to_field_elements(&bits[to_skip..])
                    .unwrap()[0]
                    == *fe
            );
            check_poly_bits.extend_from_slice(&bits[to_skip..]);
        }
        fes.append(&mut check_poly_bits.to_field_elements()?);

        // Convert the pre-previous acc into native field elements.

        // The final_comm_key of the pre-previous node is in G1, hence over G2::ScalarField.
        // We serialize them all to bits and pack them safely into native field elements
        let final_comm_key_g1 = self.pre_previous_acc.final_comm_key.clone();
        let mut final_comm_key_g1_bits = Vec::new();
        let c_fes = final_comm_key_g1.to_field_elements()?;
        for fe in c_fes {
            final_comm_key_g1_bits.append(&mut fe.write_bits());
        }
        fes.append(&mut final_comm_key_g1_bits.to_field_elements()?);

        // Although the xi's of the pre-previous node are by default 128 bit elements from G1::ScalarField
        // (we do field arithmetics with them lateron) we do not want waste space.
        // As for the xi's of the previous node, we serialize them all to bits and pack them into native
        // field elements as efficient as possible (yet secure).
        let mut check_poly_bits = Vec::new();
        for fe in self.pre_previous_acc.check_poly.chals.iter() {
            let bits = fe.write_bits();
            // write_bits() outputs a Big Endian bit order representation of fe and the same
            // expects [bool].to_field_elements(): therefore we need to take the last 128 bits,
            // e.g. we need to skip the first MODULUS_BITS - 128 bits.
            debug_assert!(
                <[bool] as ToConstraintField<G1::ScalarField>>::to_field_elements(&bits[to_skip..])
                    .unwrap()[0]
                    == *fe
            );
            check_poly_bits.extend_from_slice(&bits[to_skip..]);
        }
        fes.append(&mut check_poly_bits.to_field_elements()?);

        Ok(fes)
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
