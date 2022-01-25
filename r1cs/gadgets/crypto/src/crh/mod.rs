use algebra::{
    Field, PrimeField
};
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use std::fmt::Debug;

use primitives::crh::{
    FieldBasedHash, FixedLengthCRH
};
use r1cs_core::{ConstraintSystem, SynthesisError};

use r1cs_std::prelude::*;

pub mod bowe_hopwood;
pub mod injective_map;
pub mod pedersen;

pub mod sbox;
pub use self::sbox::*;

pub mod poseidon;
pub use self::poseidon::*;
use primitives::{AlgebraicSponge, SpongeMode};

pub trait FixedLengthCRHGadget<H: FixedLengthCRH, ConstraintF: Field>: Sized {
    type OutputGadget: EqGadget<ConstraintF>
    + ToBytesGadget<ConstraintF>
    + CondSelectGadget<ConstraintF>
    + AllocGadget<H::Output, ConstraintF>
    + Debug
    + Clone
    + Sized;
    type ParametersGadget: AllocGadget<H::Parameters, ConstraintF> + Clone;

    fn check_evaluation_gadget<CS: ConstraintSystem<ConstraintF>>(
        cs: CS,
        parameters: &Self::ParametersGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError>;
}

pub trait FieldBasedHashGadget<H: FieldBasedHash<Data = ConstraintF>, ConstraintF: Field>: Sized {
    type DataGadget: FieldGadget<ConstraintF, ConstraintF>;

    fn enforce_hash_constant_length<CS: ConstraintSystem<ConstraintF>>(
        cs: CS,
        input: &[Self::DataGadget],
    ) -> Result<Self::DataGadget, SynthesisError>;
}

pub trait FieldHasherGadget<
    H: FieldBasedHash<Data = ConstraintF>,
    ConstraintF: Field,
    HG: FieldBasedHashGadget<H, ConstraintF>
>
{
    fn enforce_hash<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        personalization: Option<&[HG::DataGadget]>
    ) -> Result<HG::DataGadget, SynthesisError>;
}

pub trait AlgebraicSpongeGadget<ConstraintF: PrimeField, H: AlgebraicSponge<ConstraintF>>:
    ConstantGadget<H, ConstraintF>
    + Sized
{
    type StateGadget;

    fn new<CS: ConstraintSystem<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError>;

    fn get_state(&self) -> &[Self::StateGadget];

    fn set_state(&mut self, state: Vec<Self::StateGadget>);

    fn get_mode(&self) -> &SpongeMode;

    fn set_mode(&mut self, mode: SpongeMode);

    fn enforce_absorb<CS: ConstraintSystem<ConstraintF>, AG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>>(
        &mut self,
        cs: CS,
        to_absorb: &AG
    ) -> Result<(), SynthesisError>;

    fn enforce_squeeze<CS: ConstraintSystem<ConstraintF>>(
        &mut self,
        cs: CS,
        num: usize
    ) -> Result<Vec<FpGadget<ConstraintF>>, SynthesisError>;
}

#[cfg(test)]
mod test {
    use algebra::PrimeField;
    use primitives::{FieldBasedHash, AlgebraicSponge};
    use rand::RngCore;
    use crate::{FieldBasedHashGadget, AlgebraicSpongeGadget};
    use r1cs_std::{
        fields::{fp::FpGadget, FieldGadget, nonnative::nonnative_field_gadget::NonNativeFieldGadget},
        test_constraint_system::TestConstraintSystem,
        alloc::AllocGadget,
    };
    use r1cs_core::ConstraintSystem;

    pub(crate) fn constant_length_field_based_hash_gadget_native_test<
        F: PrimeField,
        H: FieldBasedHash<Data = F>,
        HG: FieldBasedHashGadget<H, F, DataGadget = FpGadget<F>>,
        R: RngCore,
    >(rng: &mut R, num_inputs: usize)
    {
        let mut cs = TestConstraintSystem::<F>::new();
        let inputs = (0..num_inputs).map(|_| F::rand(rng)).collect::<Vec<_>>();

        let primitive_result = {
            let mut digest = H::init_constant_length(inputs.len(), None);
            inputs.iter().for_each(|elem| { digest.update(*elem); });
            digest.finalize().unwrap()
        };

        let mut input_gadgets = Vec::with_capacity(inputs.len());
        inputs.into_iter().enumerate().for_each(|(i, elem)| {
            let elem_gadget = HG::DataGadget::alloc(
                cs.ns(|| format!("alloc input {}", i)),
                || Ok(elem)
            ).unwrap();
            input_gadgets.push(elem_gadget);
        });

        let gadget_result = HG::enforce_hash_constant_length(
            cs.ns(|| "check_poseidon_gadget"),
            input_gadgets.as_slice()
        ).unwrap();

        assert_eq!(primitive_result, gadget_result.value.unwrap());

        if !cs.is_satisfied(){
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

        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        // Check equality between primitive and gadget result
        let mut primitive_sponge = H::init();
        primitive_sponge.absorb(&native_inputs);
        primitive_sponge.absorb(&nonnative_inputs);

        // Allocate native
        let mut native_input_gadgets = Vec::with_capacity(num_inputs);
        native_inputs.into_iter().enumerate().for_each(|(i, elem)|{
            let elem_gadget = FpGadget::<ConstraintF>::alloc(
                cs.ns(|| format!("alloc native input {}", i)),
                || Ok(elem.clone())
            ).unwrap();
            native_input_gadgets.push(elem_gadget);
        });

        // Allocate nonnative
        let mut nonnative_input_gadgets = Vec::with_capacity(num_inputs);
        nonnative_inputs.into_iter().enumerate().for_each(|(i, elem)|{
            let elem_gadget = NonNativeFieldGadget::<F, ConstraintF>::alloc(
                cs.ns(|| format!("alloc nonnative input {}", i)),
                || Ok(elem.clone())
            ).unwrap();
            nonnative_input_gadgets.push(elem_gadget);
        });

        // Enforce absorption
        let mut sponge_gadget = HG::new(cs.ns(|| "new poseidon sponge")).unwrap();
        sponge_gadget.enforce_absorb(cs.ns(|| "absorb native inputs"), &native_input_gadgets).unwrap();
        sponge_gadget.enforce_absorb(cs.ns(|| "absorb nonnative inputs"), &nonnative_input_gadgets).unwrap();

        // Enforce squeeze
        for i in 0..num_inputs {
            let output_gadgets = sponge_gadget.enforce_squeeze(
                cs.ns(|| format!("squeeze {} field elements",  i + 1)),
                i + 1
            ).unwrap().iter().map(|fe_gadget| fe_gadget.get_value().unwrap()).collect::<Vec<_>>();
            assert_eq!(output_gadgets, primitive_sponge.squeeze(i + 1));
        }

        // Check squeeze() outputs the correct number of field elements
        // all different from each others
        let mut set = HashSet::new();
        for i in 0..=10 {

            let outs = sponge_gadget.enforce_squeeze(
                cs.ns(|| format!("test squeeze {} field elements",  i)),
                i
            ).unwrap();
            assert_eq!(i, outs.len());

            // HashSet::insert(val) returns false if val was already present, so to check
            // that all the elements output by the sponge are different, we assert insert()
            // returning always true
            outs.into_iter().for_each(|f| assert!(set.insert(f.get_value().unwrap())));
        }

        assert!(cs.is_satisfied());
    }
}