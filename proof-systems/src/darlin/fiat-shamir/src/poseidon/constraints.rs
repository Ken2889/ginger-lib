use algebra::PrimeField;
use primitives::PoseidonParameters;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_crypto::{AlgebraicSpongeGadget, density_optimized::DensityOptimizedPoseidonQuinticSboxSpongeGadget, DensityOptimizedPoseidonQuinticSBoxParameters};
use r1cs_std::{to_field_gadget_vec::ToConstraintFieldGadget, fields::fp::FpGadget, boolean::Boolean, prelude::ConstantGadget};
use std::{marker::PhantomData, convert::TryInto};

use crate::{constraints::FiatShamirRngGadget, FiatShamirRng};

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
)]
pub struct PoseidonFSRngGadget<
    ConstraintF: PrimeField,
    FS: FiatShamirRng<State = Vec<ConstraintF>>,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>,
> 
{
    sponge_g: DensityOptimizedPoseidonQuinticSboxSpongeGadget<ConstraintF, P, DOP>,
    _fs: PhantomData<FS>,
}

impl<ConstraintF, FS, P, DOP> FiatShamirRngGadget<ConstraintF> for PoseidonFSRngGadget<ConstraintF, FS, P, DOP>
    where
        ConstraintF: PrimeField,
        FS:          FiatShamirRng<State = Vec<ConstraintF>>,
        P:           PoseidonParameters<Fr = ConstraintF>,
        DOP:         DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
{
    fn init<CS: ConstraintSystemAbstract<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError> {
        Ok(
            Self {
                sponge_g: DensityOptimizedPoseidonQuinticSboxSpongeGadget::<ConstraintF, P, DOP>::new(cs)?,
               _fs: PhantomData
            }
        )
    }

    fn init_from_seed<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        seed: Vec<u8>
    ) -> Result<Self, SynthesisError> {
        // Create primitive instance from seed and get the state afterwards
        let primitive_fs_rng = FS::from_seed(seed)
            .map_err(|e| SynthesisError::Other(e.to_string()))?;
        let state = primitive_fs_rng.get_state();
        
        // Create new circuit instance
        let mut gadget_fs_rng = Self::init(cs.ns(|| "create new instance"))?;

        // Hardcode inital state
        let state = Vec::<FpGadget<ConstraintF>>::from_value(
            cs.ns(|| "hardcode initial state"),
            &state
        );

        // Set state
        gadget_fs_rng.sponge_g.set_state(state);

        // Return new instance
        Ok(gadget_fs_rng) 
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
        
        self.sponge_g.enforce_absorb(cs, to_absorb)
    }

    fn enforce_squeeze_challenges<CS: ConstraintSystemAbstract<ConstraintF>, const N: usize>(
        &mut self,
        mut cs: CS,
        num: usize
    ) -> Result<Vec<[Boolean; N]>, SynthesisError> {
        let chal_bits = self.sponge_g.enforce_squeeze_bits(
            cs.ns(|| format!("squeeze {} N bits chals", num)),
            N * num
        )?;

        Ok(
            chal_bits
                .chunks_exact(N)
                .map(|chunk| chunk.to_vec().try_into().unwrap())
                .collect()
        )
    }   
}

use algebra::fields::tweedle::Fr as TweedleFr;
use primitives::crh::poseidon::parameters::tweedle_dee::TweedleFrPoseidonParameters;
use crate::poseidon::TweedleFrPoseidonFSRng;
use r1cs_crypto::dee::TweedleFrDensityOptimizedPoseidonParameters;

pub type TweedleFrPoseidonFSRngGadget = PoseidonFSRngGadget<
    TweedleFr,
    TweedleFrPoseidonFSRng,
    TweedleFrPoseidonParameters,
    TweedleFrDensityOptimizedPoseidonParameters
>;

use algebra::fields::tweedle::Fq as TweedleFq;
use primitives::crh::poseidon::parameters::tweedle_dum::TweedleFqPoseidonParameters;
use crate::poseidon::TweedleFqPoseidonFSRng;
use r1cs_crypto::dum::TweedleFqDensityOptimizedPoseidonParameters;

pub type TweedleFqPoseidonFSRngGadget = PoseidonFSRngGadget<
    TweedleFq,
    TweedleFqPoseidonFSRng,
    TweedleFqPoseidonParameters,
    TweedleFqDensityOptimizedPoseidonParameters
>;

#[cfg(test)]
mod test {
    use algebra::{Curve, UniformRand};
    use r1cs_core::{ConstraintSystem, ConstraintSystemAbstract, SynthesisMode, ConstraintSystemDebugger};
    use r1cs_std::{fields::{fp::FpGadget, nonnative::nonnative_field_gadget::NonNativeFieldGadget}, alloc::AllocGadget, prelude::UInt8};
    use rand::{RngCore, Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use crate::FiatShamirRng;

    use super::*;

    fn test_native_result<
        G:   Curve,
        FS:  FiatShamirRng,
        FSG: FiatShamirRngGadget<G::BaseField>,
        R: RngCore
    >(rng: &mut R, num_inputs: usize, initial_seed: Option<Vec<u8>>)
    {
        // Generate test data
        let native_inputs: Vec<G::BaseField> = (0..num_inputs).map(|_| G::BaseField::rand(rng)).collect();
        let nonnative_inputs: Vec<G::ScalarField> = (0..num_inputs).map(|_| G::ScalarField::rand(rng)).collect();
        let byte_inputs: Vec<u8> = (0..num_inputs * 10).map(|_| rng.gen()).collect();

        let mut cs = ConstraintSystem::<G::BaseField>::new(SynthesisMode::Debug);

        // Alloc data
        let native_inputs_g = native_inputs
            .iter()
            .enumerate()
            .map(|(i, fe)| 
                FpGadget::<G::BaseField>::alloc(
                    cs.ns(|| format!("alloc native input {}", i)),
                    || Ok(fe)
                ).unwrap()
            ).collect::<Vec<_>>();

        let nonnative_inputs_g = nonnative_inputs
            .iter()
            .enumerate()
            .map(|(i, fe)| 
                NonNativeFieldGadget::<G::ScalarField, G::BaseField>::alloc(
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
        let mut fs_rng = if let Some(seed) = initial_seed.clone() {
            FS::from_seed(seed).unwrap()
        } else {
            FS::default()
        };
        fs_rng.absorb(nonnative_inputs).unwrap();

        // Create a circuit FS rng and absorb nonnative inputs
        let mut fs_rng_g = if let Some(seed) = initial_seed.clone() {
            FSG::init_from_seed(cs.ns(|| "new fs_rng_g from seed for non native inputs"), seed).unwrap()
        } else {
            FSG::init(cs.ns(|| "new fs_rng_g for non native inputs")).unwrap()
        };
        fs_rng_g.enforce_absorb(cs.ns(|| "enforce absorb non native field elements"), nonnative_inputs_g.as_slice()).unwrap();

        // Squeeze from primitive and circuit FS rng and assert equality
        assert_eq!(
            fs_rng
                .squeeze_challenge::<128>()
                .unwrap()
                .to_vec()
            ,
            fs_rng_g.enforce_squeeze_challenges::<_, 128>(
                cs.ns(|| "squeeze 128 bits given non native absorb"), 1
            )
                .unwrap()[0]
                .iter()
                .map(|bit_g| bit_g.get_value().unwrap())
                .collect::<Vec<_>>()
        );

        // Test Native inputs

        // Create a primitive FS rng and absorb native inputs
        let mut fs_rng = if let Some(seed) = initial_seed.clone() {
            FS::from_seed(seed).unwrap()
        } else {
            FS::default()
        };
        fs_rng.absorb(native_inputs).unwrap();   

        // Create a circuit FS rng and absorb native inputs
        let mut fs_rng_g = if let Some(seed) = initial_seed.clone() {
            FSG::init_from_seed(cs.ns(|| "new fs_rng_g from seed for native inputs"), seed).unwrap()
        } else {
            FSG::init(cs.ns(|| "new fs_rng_g for native inputs")).unwrap()
        };
        fs_rng_g.enforce_absorb(cs.ns(|| "enforce absorb native field elements"), native_inputs_g).unwrap();

        // Squeeze from primitive and circuit FS rng and assert equality
        assert_eq!(
            fs_rng
                .squeeze_challenge::<128>()
                .unwrap()
                .to_vec()
            ,
            fs_rng_g.enforce_squeeze_challenges::<_, 128>(
                cs.ns(|| "squeeze 128 bits given native absorb"), 1
            )
                .unwrap()[0]
                .iter()
                .map(|bit_g| bit_g.get_value().unwrap())
                .collect::<Vec<_>>()
        );

        // Test byte inputs

        // Create a primitive FS rng and absorb byte inputs
        let mut fs_rng = if let Some(seed) = initial_seed.clone() {
            FS::from_seed(seed).unwrap()
        } else {
            FS::default()
        };
        fs_rng.absorb::<G::BaseField, _>(byte_inputs.as_slice()).unwrap();

        // Create a circuit FS rng and absorb byte inputs
        let mut fs_rng_g = if let Some(seed) = initial_seed {
            FSG::init_from_seed(cs.ns(|| "new fs_rng_g from seed for byte inputs"), seed).unwrap()
        } else {
            FSG::init(cs.ns(|| "new fs_rng_g for byte inputs")).unwrap()
        };
        fs_rng_g.enforce_absorb(cs.ns(|| "enforce absorb byte elements"), byte_inputs_g.as_slice()).unwrap();

        // Squeeze from primitive and circuit FS rng and assert equality
        assert_eq!(
            fs_rng
                .squeeze_challenge::<128>()
                .unwrap()
                .to_vec()
            ,
            fs_rng_g.enforce_squeeze_challenges::<_, 128>(
                cs.ns(|| "squeeze 128 bits given byte absorb"), 1
            )
                .unwrap()[0]
                .iter()
                .map(|bit_g| bit_g.get_value().unwrap())
                .collect::<Vec<_>>()
        );

        if !cs.is_satisfied(){
            println!("{:?}", cs.which_is_unsatisfied());
        }

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_tweedle_dum() {
        use algebra::curves::tweedle::dum::DumJacobian as TweedleDum;
        use super::*;

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        for seed in vec![None, Some(b"TEST_SEED".to_vec())] {
            for i in 1..=5 {
                test_native_result::<TweedleDum, TweedleFrPoseidonFSRng, TweedleFrPoseidonFSRngGadget, _>(rng, i, seed.clone());
            }
        }
        
    }

    #[test]
    fn test_tweedle_dee() {
        use algebra::curves::tweedle::dee::DeeJacobian as TweedleDee;
        use super::*;

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        for seed in vec![None, Some(b"TEST_SEED".to_vec())] {
            for i in 1..=5 {
                test_native_result::<TweedleDee, TweedleFqPoseidonFSRng, TweedleFqPoseidonFSRngGadget, _>(rng, i, seed.clone());
            }
        }
    }
}