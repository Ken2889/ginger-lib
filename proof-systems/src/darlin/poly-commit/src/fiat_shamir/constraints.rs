/// the trait for Fiat-Shamir RNG Gadget
pub trait FiatShamirRngGadget<ConstraintF: PrimeField>:
    Sized
    + Clone
{
    /// initialize an empty transcript
    fn init<CS: ConstraintSystem<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError>;

    /// initialize from a seed
    fn init_from_seed<CS: ConstraintSystem<ConstraintF>>(
        cs: CS,
        seed: Vec<ConstraintF>
    ) -> Result<Self, SynthesisError>;

    /// take in field elements
    fn enforce_absorb<
        CS: ConstraintSystemAbstract<ConstraintF>,
        T: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>>(
            &mut self,
            cs: CS,
            elems: &[T]
    ) -> Result<(), SynthesisError>;

    /// take in bytes
    fn enforce_absorb_bytes<CS: ConstraintSystem<ConstraintF>>(
        &mut self,
        cs: CS,
        elems: &[UInt8]
    ) -> Result<(), SynthesisError>;

    /// Output field elements
    fn enforce_squeeze<CS: ConstraintSystem<ConstraintF>>(
        &mut self,
        cs: CS,
        num: usize
    ) -> Result<Vec<FpGadget<ConstraintF>>, SynthesisError>;

    /// Output non-native field elements of 128 bits
    fn enforce_squeeze_128_bits_challenges<CS: ConstraintSystem<ConstraintF>>(
        &mut self,
        cs: CS,
        num: usize
    ) -> Result<Vec<Vec<Boolean>>, SynthesisError>;
}