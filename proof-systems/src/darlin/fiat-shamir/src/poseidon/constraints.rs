use std::convert::TryInto;

use algebra::PrimeField;
use primitives::PoseidonParameters;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_crypto::{AlgebraicSpongeGadget, density_optimized::{DensityOptimizedPoseidonQuinticSboxSpongeGadget, S}, DensityOptimizedPoseidonQuinticSBoxParameters};
use r1cs_std::{to_field_gadget_vec::ToConstraintFieldGadget, fields::fp::FpGadget, boolean::Boolean, prelude::ConstantGadget};

use crate::constraints::FiatShamirRngGadget;

impl<ConstraintF, P, DOP> FiatShamirRngGadget<ConstraintF> for DensityOptimizedPoseidonQuinticSboxSpongeGadget<ConstraintF, P, DOP>
    where
        ConstraintF: PrimeField,
        P:           PoseidonParameters<Fr = ConstraintF>,
        DOP:         DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
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
        to_absorb: AG
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        AG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>
    {
        
        <Self as AlgebraicSpongeGadget<ConstraintF, S<ConstraintF, P>>>::enforce_absorb(self, cs, to_absorb)
    }

    fn enforce_squeeze<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        cs: CS,
        num: usize
    ) -> Result<Vec<FpGadget<ConstraintF>>, SynthesisError> {
        <Self as AlgebraicSpongeGadget<ConstraintF, S<ConstraintF, P>>>::enforce_squeeze(self, cs, num)
    }

    fn enforce_squeeze_128_bits_challenges<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS,
        num: usize
    ) -> Result<Vec<[Boolean; 128]>, SynthesisError> {
        (0..num).map(|i| {
            let chal_bits = <Self as AlgebraicSpongeGadget<ConstraintF, S<ConstraintF, P>>>::enforce_squeeze_bits(
                self,
                cs.ns(|| format!("squeeze 128 bits chal {}", i)),
                128
            )?;

            let chal_bits: [Boolean; 128] = chal_bits.try_into().unwrap(); // Cannot fail as we explicitly squeeze 128 bits

            Ok(chal_bits)
        }).collect()   
    }
}

#[cfg(test)]
mod test {
    use algebra::{EndoMulCurve, Field, UniformRand};
    use r1cs_core::{ConstraintSystem, ConstraintSystemAbstract, SynthesisMode, ConstraintSystemDebugger};
    use r1cs_std::{fields::{fp::FpGadget, nonnative::nonnative_field_gadget::NonNativeFieldGadget, FieldGadget}, alloc::AllocGadget, prelude::UInt8};
    use rand::{RngCore, Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use crate::FiatShamirRng;

    use super::FiatShamirRngGadget;

    fn test_native_result<
        G: EndoMulCurve,
        FS:  FiatShamirRng,
        FSG: FiatShamirRngGadget<<G::BaseField as Field>::BasePrimeField>,
        R: RngCore
    >(rng: &mut R, num_inputs: usize)
    {
        // Generate test data
        let native_inputs: Vec<<G::BaseField as Field>::BasePrimeField> = (0..num_inputs).map(|_| <G::BaseField as Field>::BasePrimeField::rand(rng)).collect();
        let nonnative_inputs: Vec<G::ScalarField> = (0..num_inputs).map(|_| G::ScalarField::rand(rng)).collect();
        let byte_inputs: Vec<u8> = (0..num_inputs * 10).map(|_| rng.gen()).collect();

        let mut cs = ConstraintSystem::<<G::BaseField as Field>::BasePrimeField>::new(SynthesisMode::Debug);

        // Alloc data
        let native_inputs_g = native_inputs
            .iter()
            .enumerate()
            .map(|(i, fe)| 
                FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc(
                    cs.ns(|| format!("alloc native input {}", i)),
                    || Ok(fe)
                ).unwrap()
            ).collect::<Vec<_>>();

        let nonnative_inputs_g = nonnative_inputs
            .iter()
            .enumerate()
            .map(|(i, fe)| 
                NonNativeFieldGadget::<G::ScalarField, <G::BaseField as Field>::BasePrimeField>::alloc(
                    cs.ns(|| format!("alloc nonnative input {}", i)),
                    || Ok(fe)
                ).unwrap()
            ).collect::<Vec<_>>();

        let byte_inputs_g = byte_inputs
        .iter()
        .enumerate()
        .map(|(i, fe)| 
            UInt8::alloc(
                cs.ns(|| format!("alloc byte input {}", i)),
                || Ok(fe)
            ).unwrap()
        ).collect::<Vec<_>>();

        // Test Non Native inputs

        // Create a primitive FS rng and absorb nonnative inputs
        let mut fs_rng = FS::default();
        fs_rng.absorb(nonnative_inputs).unwrap();

        // Create a circuit FS rng and absorb nonnative inputs
        let mut fs_rng_g = FSG::init(cs.ns(|| "new fs_rng_g for non native inputs")).unwrap();
        fs_rng_g.enforce_absorb(cs.ns(|| "enforce absorb non native field elements"), nonnative_inputs_g.as_slice()).unwrap();

        // Squeeze from primitive and circuit FS rng and assert equality
        assert_eq!(
            (
                fs_rng.squeeze(),
                fs_rng.squeeze_128_bits_challenge::<G>(),
            ),
            (
                fs_rng_g.enforce_squeeze(
                    cs.ns(||"squeeze native given non native absorb"), 1
                ).unwrap()[0].get_value().unwrap(),
                G::endo_rep_to_scalar(
                    fs_rng_g.enforce_squeeze_128_bits_challenges(
                        cs.ns(|| "squeeze 128 bits given non native absorb"), 1
                    ).unwrap()[0]
                    .iter()
                    .map(|bit_g| bit_g.get_value().unwrap())
                    .collect::<Vec<_>>()
                ).unwrap(),
            )
        );

        // Test Native inputs

        // Create a primitive FS rng and absorb native inputs
        let mut fs_rng = FS::default();
        fs_rng.absorb(native_inputs).unwrap();   

        // Create a circuit FS rng and absorb native inputs
        let mut fs_rng_g = FSG::init(cs.ns(|| "new fs_rng_g for native inputs")).unwrap();
        fs_rng_g.enforce_absorb(cs.ns(|| "enforce absorb native field elements"), native_inputs_g).unwrap();

        // Squeeze from primitive and circuit FS rng and assert equality
        assert_eq!(
            (
                fs_rng.squeeze(),
                fs_rng.squeeze_128_bits_challenge::<G>(),
            ),
            (
                fs_rng_g.enforce_squeeze(
                    cs.ns(||"squeeze native given native absorb"), 1
                ).unwrap()[0].get_value().unwrap(),
                G::endo_rep_to_scalar(
                    fs_rng_g.enforce_squeeze_128_bits_challenges(
                        cs.ns(|| "squeeze 128 bits given native absorb"), 1
                    ).unwrap()[0]
                    .iter()
                    .map(|bit_g| bit_g.get_value().unwrap())
                    .collect::<Vec<_>>()
                ).unwrap(),
            )
        );

        // Test byte inputs

        // Create a primitive FS rng and absorb byte inputs
        let mut fs_rng = FS::default();
        fs_rng.absorb::<<G::BaseField as Field>::BasePrimeField, _>(byte_inputs.as_slice()).unwrap();

        // Create a circuit FS rng and absorb byte inputs
        let mut fs_rng_g = FSG::init(cs.ns(|| "new fs_rng_g for byte inputs")).unwrap();
        fs_rng_g.enforce_absorb(cs.ns(|| "enforce absorb byte elements"), byte_inputs_g.as_slice()).unwrap();

        // Squeeze from primitive and circuit FS rng and assert equality
        assert_eq!(
            (
                fs_rng.squeeze(),
                fs_rng.squeeze_128_bits_challenge::<G>(),
            ),
            (
                fs_rng_g.enforce_squeeze(
                    cs.ns(||"squeeze native given byte absorb"), 1
                ).unwrap()[0].get_value().unwrap(),
                G::endo_rep_to_scalar(
                    fs_rng_g.enforce_squeeze_128_bits_challenges(
                        cs.ns(|| "squeeze 128 bits given byte absorb"), 1
                    ).unwrap()[0]
                    .iter()
                    .map(|bit_g| bit_g.get_value().unwrap())
                    .collect::<Vec<_>>()
                ).unwrap(),
            )
        );

        if !cs.is_satisfied(){
            println!("{:?}", cs.which_is_unsatisfied());
        }

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_tweedle_dee() {
        use algebra::curves::tweedle::dee::DeeJacobian as TweedleDee;
        use primitives::crh::poseidon::TweedleFqPoseidonSponge;
        use r1cs_crypto::crh::poseidon::TweedleFqDensityOptimizedPoseidonSpongeGadget;

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        for i in 0..=5 {
            test_native_result::<TweedleDee, TweedleFqPoseidonSponge, TweedleFqDensityOptimizedPoseidonSpongeGadget, _>(rng, i);
        }
    }

    #[test]
    fn test_tweedle_dum() {
        use algebra::curves::tweedle::dum::DumJacobian as TweedleDum;
        use primitives::crh::poseidon::TweedleFrPoseidonSponge;
        use r1cs_crypto::crh::poseidon::TweedleFrDensityOptimizedPoseidonSpongeGadget;

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        for i in 0..=5 {
            test_native_result::<TweedleDum, TweedleFrPoseidonSponge, TweedleFrDensityOptimizedPoseidonSpongeGadget, _>(rng, i);
        }
    }
}