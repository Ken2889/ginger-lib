use algebra::{Field, PrimeField, FpParameters};
use primitives::AlgebraicSponge;
use primitives::SpongeMode;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use std::fmt::Debug;

use primitives::crh::{FieldBasedHash, FixedLengthCRH};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};

use r1cs_std::prelude::*;

pub mod bowe_hopwood;
pub mod injective_map;
pub mod pedersen;

pub mod sbox;
pub use self::sbox::*;

pub mod poseidon;
pub use self::poseidon::*;

pub trait FixedLengthCRHGadget<H: FixedLengthCRH, ConstraintF: Field>: Sized {
    type OutputGadget: EqGadget<ConstraintF>
        + ToBytesGadget<ConstraintF>
        + CondSelectGadget<ConstraintF>
        + AllocGadget<H::Output, ConstraintF>
        + Debug
        + Clone
        + Sized;
    type ParametersGadget: AllocGadget<H::Parameters, ConstraintF> + Clone;

    fn check_evaluation_gadget<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        parameters: &Self::ParametersGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError>;
}

pub trait FieldBasedHashGadget<H: FieldBasedHash<Data = ConstraintF>, ConstraintF: Field>:
    Sized
{
    type DataGadget: FieldGadget<ConstraintF, ConstraintF>;

    fn enforce_hash_constant_length<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        input: &[Self::DataGadget],
    ) -> Result<Self::DataGadget, SynthesisError>;
}

pub trait FieldHasherGadget<
    H: FieldBasedHash<Data = ConstraintF>,
    ConstraintF: Field,
    HG: FieldBasedHashGadget<H, ConstraintF>,
>
{
    fn enforce_hash<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        personalization: Option<&[HG::DataGadget]>,
    ) -> Result<HG::DataGadget, SynthesisError>;
}

pub trait AlgebraicSpongeGadget<ConstraintF: PrimeField, H: AlgebraicSponge<ConstraintF>>:
    ConstantGadget<H, ConstraintF>
    + From<Vec<FpGadget<ConstraintF>>>
    + Sized
{
    type StateGadget: Clone + Debug + Eq + PartialEq;

    /// Enforce initialization the sponge in absorbing mode
    fn new<CS: ConstraintSystemAbstract<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError>;

    /// Get the sponge internal state
    fn get_state(&self) -> Vec<Self::StateGadget>;

    /// Set the sponge internal state
    fn set_state(&mut self, state: Vec<Self::StateGadget>);

    /// Get Sponge current operating mode
    fn get_mode(&self) -> &SpongeMode;

    /// Set Sponge current operating mode
    fn set_mode(&mut self, mode: SpongeMode);

    /// Enforce absorbption of field gadgets belonging to ConstraintF.
    fn enforce_absorb<CS, AG>(
        &mut self,
        cs: CS,
        to_absorb: AG
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        AG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>;

    /// Enforce squeezing of 'num' field gadgets belonging to ConstraintF.
    fn enforce_squeeze<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        cs: CS,
        num: usize
    ) -> Result<Vec<FpGadget<ConstraintF>>, SynthesisError>;

    /// Enforce squeezing of 'num_bits' Booleans.
    fn enforce_squeeze_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS,
        num_bits: usize
    ) -> Result<Vec<Boolean>, SynthesisError> 
    {
        // We return a certain amount of bits by squeezing field elements instead,
        // serialize them and return their bits.

        // Smallest number of field elements to squeeze to reach 'num_bits' is ceil(num_bits/FIELD_CAPACITY).
        // This is done to achieve uniform distribution over the output space, and it also
        // comes handy as in the circuit we don't need to enforce range proofs for them.
        let usable_bits = ConstraintF::Params::CAPACITY as usize; 
        let num_elements = (num_bits + usable_bits - 1) / usable_bits;
        let src_elements = self.enforce_squeeze(
            cs.ns(|| "squeeze fes to be serialized"),
            num_elements
        )?;

        // Serialize field elements into bits and return them
        let mut dest_bits: Vec<Boolean> = Vec::with_capacity(usable_bits * num_elements);
    
        // discard modulus - capacity bits
        let to_skip =  ConstraintF::Params::MODULUS_BITS as usize - usable_bits; 
        for (i, elem) in src_elements.into_iter().enumerate() {
            let mut elem_bits = elem.to_bits_with_length_restriction(
                cs.ns(|| format!("elem {} to bits", i)),
                to_skip
            )?;
            dest_bits.append(&mut elem_bits);
        }
        Ok(dest_bits[..num_bits].to_vec())
    }
}

#[cfg(test)]
mod test {
    use crate::{FieldBasedHashGadget, AlgebraicSpongeGadget};
    use algebra::PrimeField;
    use primitives::{FieldBasedHash, AlgebraicSponge, SpongeMode};
    use r1cs_core::{
        ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
    };
    use r1cs_std::{
        alloc::AllocGadget,
        fields::{FieldGadget, fp::FpGadget, nonnative::nonnative_field_gadget::NonNativeFieldGadget}, prelude::UInt8,
    };
    use rand::{RngCore, Rng};

    pub(crate) fn constant_length_field_based_hash_gadget_native_test<
        F: PrimeField,
        H: FieldBasedHash<Data = F>,
        HG: FieldBasedHashGadget<H, F, DataGadget = FpGadget<F>>,
        R: RngCore,
    >(rng: &mut R, num_inputs: usize)
    {
        let mut cs = ConstraintSystem::<F>::new(SynthesisMode::Debug);
        let inputs = (0..num_inputs).map(|_| F::rand(rng)).collect::<Vec<_>>();

        let primitive_result = {
            let mut digest = H::init_constant_length(inputs.len(), None);
            inputs.iter().for_each(|elem| {
                digest.update(*elem);
            });
            digest.finalize().unwrap()
        };

        let mut input_gadgets = Vec::with_capacity(inputs.len());
        inputs.into_iter().enumerate().for_each(|(i, elem)| {
            let elem_gadget =
                HG::DataGadget::alloc(cs.ns(|| format!("alloc input {}", i)), || Ok(elem)).unwrap();
            input_gadgets.push(elem_gadget);
        });

        let gadget_result = HG::enforce_hash_constant_length(
            cs.ns(|| "check_poseidon_gadget"),
            input_gadgets.as_slice(),
        )
        .unwrap();

        assert_eq!(primitive_result, gadget_result.value.unwrap());

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
    }

    pub(crate) fn algebraic_sponge_gadget_test<
        F: PrimeField,
        ConstraintF: PrimeField,
        H: AlgebraicSponge<ConstraintF>,
        HG: AlgebraicSpongeGadget<ConstraintF, H>,
        R: RngCore
    >(rng: &mut R, num_inputs: usize)
    {
        use std::collections::HashSet;

        // Generate inputs
        let native_inputs = (0..num_inputs).map(|_| ConstraintF::rand(rng)).collect::<Vec<_>>();
        let nonnative_inputs = (0..num_inputs).map(|_| F::rand(rng)).collect::<Vec<_>>();
        let byte_inputs = (0..num_inputs * 10).map(|_| rng.gen()).collect::<Vec<u8>>();

        let mut cs = ConstraintSystem::<ConstraintF>::new(SynthesisMode::Debug);

        // Allocate native
        let mut native_input_gadgets = Vec::with_capacity(num_inputs);
        native_inputs.iter().enumerate().for_each(|(i, elem)|{
            let elem_gadget = FpGadget::<ConstraintF>::alloc(
                cs.ns(|| format!("alloc native input {}", i)),
                || Ok(elem)
            ).unwrap();
            native_input_gadgets.push(elem_gadget);
        });

        // Allocate nonnative
        let mut nonnative_input_gadgets = Vec::with_capacity(num_inputs);
        nonnative_inputs.iter().enumerate().for_each(|(i, elem)|{
            let elem_gadget = NonNativeFieldGadget::<F, ConstraintF>::alloc(
                cs.ns(|| format!("alloc nonnative input {}", i)),
                || Ok(elem)
            ).unwrap();
            nonnative_input_gadgets.push(elem_gadget);
        });

        // Allocate bytes
        let mut byte_input_gadgets = Vec::with_capacity(num_inputs * 10);
        byte_inputs.iter().enumerate().for_each(|(i, elem)|{
            let elem_gadget = UInt8::alloc(
                cs.ns(|| format!("alloc byte input {}", i)),
                || Ok(elem)
            ).unwrap();
            byte_input_gadgets.push(elem_gadget);
        });

        // Check equality between primitive and gadget result
        let mut primitive_sponge = H::init();
        primitive_sponge.absorb(native_inputs.clone()).unwrap();
        primitive_sponge.absorb(nonnative_inputs).unwrap();
        primitive_sponge.absorb::<ConstraintF, _>(byte_inputs.as_slice()).unwrap();

        // Enforce absorption
        let mut sponge_gadget = HG::new(cs.ns(|| "new poseidon sponge")).unwrap();
        assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Absorbing));

        sponge_gadget.enforce_absorb(cs.ns(|| "absorb native inputs"), native_input_gadgets.clone()).unwrap();
        assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Absorbing));

        sponge_gadget.enforce_absorb(cs.ns(|| "absorb nonnative inputs"), nonnative_input_gadgets.as_slice()).unwrap();
        assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Absorbing));

        sponge_gadget.enforce_absorb(cs.ns(|| "absorb byte inputs"), byte_input_gadgets.as_slice()).unwrap();
        assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Absorbing));

        // Enforce squeeze
        for i in 1..num_inputs {
            // Absorb again
            primitive_sponge.absorb(native_inputs[..i].to_vec()).unwrap();
            sponge_gadget.enforce_absorb(
                cs.ns(|| format!("test 1: squeeze {} field elements, absorbing phase",  i)),
                native_input_gadgets[..i].to_vec()
            ).unwrap();
            assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Absorbing));

            // Test squeeze
            let output_gadgets = sponge_gadget.enforce_squeeze(
                cs.ns(|| format!("test 1: squeeze {} field elements",  i)),
                i
            ).unwrap().iter().map(|fe_gadget| fe_gadget.get_value().unwrap()).collect::<Vec<_>>();
            assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Squeezing));
            assert_eq!(output_gadgets, primitive_sponge.squeeze(i).unwrap());
        }

        // Enforce squeeze bits
        for i in 1..num_inputs {
            // Absorb again
            primitive_sponge.absorb(native_inputs[..i].to_vec()).unwrap();
            sponge_gadget.enforce_absorb(
                cs.ns(|| format!("test 1: squeeze {} bits, absorbing phase",  i)),
                native_input_gadgets[..i].to_vec()
            ).unwrap();
            assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Absorbing));

            // Test squeeze bits
            let output_gadgets = sponge_gadget.enforce_squeeze_bits(
                cs.ns(|| format!("test 1: squeeze {} bits",  i * 10)),
                i * 10
            ).unwrap().iter().map(|bit_g| bit_g.get_value().unwrap()).collect::<Vec<_>>();
            assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Squeezing));
            assert_eq!(output_gadgets, primitive_sponge.squeeze_bits(i * 10).unwrap());
        }

        // Check squeeze() outputs the correct number of field elements
        // all different from each others
        let mut set = HashSet::new();
        for i in 1..=10 {

            let outs = sponge_gadget.enforce_squeeze(
                cs.ns(|| format!("test 2: squeeze {} field elements",  i)),
                i
            ).unwrap();
            assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Squeezing));
            assert_eq!(i, outs.len());

            // HashSet::insert(val) returns false if val was already present, so to check
            // that all the elements output by the sponge are different, we assert insert()
            // returning always true
            outs.into_iter().for_each(|f| assert!(set.insert(f.get_value().unwrap())));
        }

        // Check squeeze_bits() outputs the correct number of bits
        for i in 1..=10 {
            let outs = sponge_gadget.enforce_squeeze_bits(
                cs.ns(|| format!("test 2: squeeze {} bits",  i * 10)),
                i * 10
            ).unwrap();
            assert_eq!(i * 10, outs.len());
            assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Squeezing));

            // Bits should all be different with overwhelming probability
            assert!(!(
                outs.iter().all(|bit_g| bit_g.get_value().unwrap())
                ||
                outs.into_iter().all(|bit_g| !bit_g.get_value().unwrap())
            ));
        }

        let prev_state = sponge_gadget.get_state();

        // Absorb nothing. Check that the internal state is not changed.
        assert!(sponge_gadget.enforce_absorb(cs.ns(|| "absorb nothing"), Vec::<FpGadget<ConstraintF>>::new()).is_err());
        assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Squeezing));
        assert_eq!(prev_state.clone(), sponge_gadget.get_state());

        // Squeeze nothing. Check that the internal state is not changed.
        assert!(sponge_gadget.enforce_squeeze(cs.ns(|| "squeeze nothing"), 0).is_err());
        assert!(matches!(sponge_gadget.get_mode(), SpongeMode::Squeezing));
        assert_eq!(prev_state, sponge_gadget.get_state());

        let is_satisfied = cs.which_is_unsatisfied();
        println!("{:?}", is_satisfied);
        assert!(is_satisfied.is_none());
    }
}
