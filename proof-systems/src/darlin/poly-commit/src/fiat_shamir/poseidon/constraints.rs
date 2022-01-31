use std::convert::TryInto;

use algebra::PrimeField;
use primitives::{PoseidonParameters, SBox, PoseidonSponge};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_crypto::{AlgebraicSpongeGadget, PoseidonSpongeGadget, SBoxGadget};
use r1cs_std::{to_field_gadget_vec::ToConstraintFieldGadget, fields::fp::FpGadget, ToBytesGadget, boolean::Boolean, prelude::ConstantGadget};

use crate::constraints::FiatShamirRngGadget;

impl<ConstraintF, P, SB, SBG> FiatShamirRngGadget<ConstraintF> for PoseidonSpongeGadget<ConstraintF, P, SB, SBG>
    where
        ConstraintF: PrimeField,
        P:           PoseidonParameters<Fr = ConstraintF>,
        SB:          SBox<Field = ConstraintF, Parameters = P>,
        SBG:         SBoxGadget<ConstraintF, SB>,
{
    fn init<CS: ConstraintSystemAbstract<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError> {
        Self::new(cs)
    }

    fn init_from_seed<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        seed: Vec<ConstraintF>
    ) -> Result<Self, SynthesisError> {
        // Create new instance
        let mut new_instance = Self::init(cs.ns(|| "create new instance"))?;

        // Hardcode inital state
        let state = Vec::<FpGadget<ConstraintF>>::from_value(
            cs.ns(|| "hardcode initial state"),
            &seed
        );

        // Set state
        new_instance.set_state(state);

        // Return new instance
        Ok(new_instance) 
    }

    fn enforce_absorb<CS, AG>(
        &mut self,
        cs: CS,
        to_absorb: &AG
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        AG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>
           + ToBytesGadget<ConstraintF> 
    {
        
        <Self as AlgebraicSpongeGadget<ConstraintF, PoseidonSponge<ConstraintF, P, SB>>>::enforce_absorb(self, cs, to_absorb)
    }

    fn enforce_squeeze<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        cs: CS,
        num: usize
    ) -> Result<Vec<FpGadget<ConstraintF>>, SynthesisError> {
        <Self as AlgebraicSpongeGadget<ConstraintF, PoseidonSponge<ConstraintF, P, SB>>>::enforce_squeeze(self, cs, num)
    }

    fn enforce_squeeze_128_bits_challenges<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS,
        num: usize
    ) -> Result<Vec<[Boolean; 128]>, SynthesisError> {
        (0..num).map(|i| {
            let chal_bits = <Self as AlgebraicSpongeGadget<ConstraintF, PoseidonSponge<ConstraintF, P, SB>>>::enforce_squeeze_bits(
                self,
                cs.ns(|| format!("squeeze 128 bits chal {}", i)),
                128
            )?;

            let chal_bits: [Boolean; 128] = chal_bits.try_into().unwrap(); // Cannot fail as we explicitly squeeze 128 bits

            Ok(chal_bits)
        }).collect()   
    }
}