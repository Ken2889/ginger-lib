use crate::poseidon::PoseidonFSRng;
use primitives::PoseidonQuinticSBox;
use algebra::{FpParameters, PrimeField};
use primitives::PoseidonParameters;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_crypto::{DensityOptimizedPoseidonQuinticSboxHashGadget, DensityOptimizedPoseidonQuinticSBoxParameters};
use r1cs_std::{to_field_gadget_vec::ToConstraintFieldGadget, fields::fp::FpGadget, boolean::Boolean, prelude::ConstantGadget};
use std::{marker::PhantomData, convert::TryInto};

use crate::{constraints::FiatShamirRngGadget, FiatShamirRng};

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct DensityOptimizedPoseidonQuinticSBoxFSRngGadget
<
    ConstraintF: PrimeField,
    P:           PoseidonParameters<Fr = ConstraintF>,
    DOP:         DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>,
>
{
    pub(crate) state: Vec<FpGadget<ConstraintF>>,
    pub(crate) pending_inputs: Vec<FpGadget<ConstraintF>>,
    pub(crate) pending_outputs: Vec<FpGadget<ConstraintF>>,
    capacity: usize,
    _parameters: PhantomData<P>,
    _density_optimized_parameters: PhantomData<DOP>,
}

impl<ConstraintF, P, DOP> DensityOptimizedPoseidonQuinticSBoxFSRngGadget<ConstraintF, P, DOP>
    where
        ConstraintF: PrimeField,
        P:           PoseidonParameters<Fr = ConstraintF>,
        DOP:         DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>,
{
    fn enforce_permutations<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS
    ) -> Result<(), SynthesisError>
    {
        if !self.pending_inputs.is_empty() {
            // Permute inputs
            DensityOptimizedPoseidonQuinticSboxHashGadget::<ConstraintF, P, DOP>::_enforce_hash_constant_length(
                cs.ns(|| "apply permutations to inputs"),
                self.pending_inputs.as_slice(),
                &mut self.state,
            )?;

            // Clear input buffer
            self.pending_inputs.clear();
        } else {
            // apply permutation to state
            DensityOptimizedPoseidonQuinticSboxHashGadget::<ConstraintF, P, DOP>::poseidon_perm(
                cs.ns(|| "permute state"),
                &mut self.state
            )?;
        }

        // Push RATE many elements from the state into the output buffer
        self.pending_outputs.extend_from_slice(&self.state[..self.capacity]);

        Ok(())
    }

    fn enforce_get_element<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        cs: CS,
    ) -> Result<FpGadget<ConstraintF>, SynthesisError>
    {
        if self.pending_outputs.is_empty() {
            self.enforce_permutations(cs)?;
        }

        Ok(self.pending_outputs.pop().unwrap())
    }

    /// Enforce squeezing of 'num_bits' Booleans.
    fn enforce_get_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS,
        num_bits: usize
    ) -> Result<Vec<Boolean>, SynthesisError> 
    {
        if num_bits == 0 {
            Err(SynthesisError::Other("No challenge to get !".to_string()))?;
        }

        // We return a certain amount of bits by retrieving field elements instead,
        // serialize them and return their bits.

        // Smallest number of field elements to retrieve to reach 'num_bits' is ceil(num_bits/FIELD_CAPACITY).
        // This is done to achieve uniform distribution over the output space, and it also
        // comes handy as in the circuit we don't need to enforce range proofs for them.
        let usable_bits = ConstraintF::Params::CAPACITY as usize; 
        let num_elements = (num_bits + usable_bits - 1) / usable_bits;
        let mut src_elements = Vec::with_capacity(num_elements);

        // Apply as many permutations as needed to get the required number of field elements
        let mut i = 0;
        while src_elements.len() != num_elements {
            src_elements.push(
                self.enforce_get_element(
                    cs.ns(|| format!("Get elem {}", i))
                )?
            );
            i += 1;
        }

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

impl<ConstraintF, P, DOP> FiatShamirRngGadget<ConstraintF> for DensityOptimizedPoseidonQuinticSBoxFSRngGadget<ConstraintF, P, DOP>
    where
    ConstraintF: PrimeField,
    P:           PoseidonParameters<Fr = ConstraintF>,
    DOP:         DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>,
{
    fn init<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS) -> Result<Self, SynthesisError> {
        let mut state = Vec::with_capacity(P::T);
        for i in 0..P::T {
            let elem = FpGadget::<ConstraintF>::from_value(
                cs.ns(|| format!("hardcode_state_{}",i)),
                &P::AFTER_ZERO_PERM[i]
            );
            state.push(elem);
        }
        let capacity = P::T - P::R;

        Ok(Self {
            state,
            pending_inputs: Vec::new(),
            pending_outputs: Vec::with_capacity(capacity),
            capacity,
            _parameters: PhantomData,
            _density_optimized_parameters: PhantomData
        })
    }

    fn init_from_seed<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        seed: Vec<u8>
    ) -> Result<Self, SynthesisError> {
        // Create primitive instance from seed and get the state afterwards
        let primitive_fs_rng = PoseidonFSRng::<ConstraintF, P, PoseidonQuinticSBox<ConstraintF, P>>::from_seed(seed)
            .map_err(|e| SynthesisError::Other(e.to_string()))?;
        
        // We can ignore the rest as they should be empty
        let (state, _, _) = primitive_fs_rng.get_state();

        // Hardcode inital state
        let state = Vec::<FpGadget<ConstraintF>>::from_value(
            cs.ns(|| "hardcode initial state"),
            &state
        );

        let capacity = P::T - P::R;

        Ok(Self {
            state,
            pending_inputs: Vec::new(),
            pending_outputs: Vec::with_capacity(capacity),
            capacity,
            _parameters: PhantomData,
            _density_optimized_parameters: PhantomData
        })
    }

    fn enforce_record<CS, RG>(
        &mut self,
        mut cs: CS,
        data: RG
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        RG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>
    {
        // Get field gadgets
        let mut elems = data.to_field_gadget_elements(cs.ns(|| "data to fes"))?;
        
        if elems.is_empty() {
            return Err(SynthesisError::Other("Noting to record !".to_string()));
        }

        // They refer to an old state, so we cannot use them anymore
        self.pending_outputs.clear();
        
        // Save new inputs to be processed
        self.pending_inputs.append(&mut elems);

        Ok(())
    }

    fn enforce_get_challenge<CS: ConstraintSystemAbstract<ConstraintF>, const N: usize>(
        &mut self,
        cs: CS,
    ) -> Result<[Boolean; N], SynthesisError> {
        Ok(self.enforce_get_many_challenges(cs, 1)?[0])
    }

    fn enforce_get_many_challenges<CS: ConstraintSystemAbstract<ConstraintF>, const N: usize>(
        &mut self,
        mut cs: CS,
        num: usize
    ) -> Result<Vec<[Boolean; N]>, SynthesisError> {
        let chal_bits = self.enforce_get_bits(
            cs.ns(|| format!("get {} N bits chals", num)),
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
use r1cs_crypto::dee::TweedleFrDensityOptimizedPoseidonParameters;

pub type TweedleFrPoseidonFSRngGadget = DensityOptimizedPoseidonQuinticSBoxFSRngGadget<
    TweedleFr,
    TweedleFrPoseidonParameters,
    TweedleFrDensityOptimizedPoseidonParameters
>;

use algebra::fields::tweedle::Fq as TweedleFq;
use primitives::crh::poseidon::parameters::tweedle_dum::TweedleFqPoseidonParameters;
use r1cs_crypto::dum::TweedleFqDensityOptimizedPoseidonParameters;

pub type TweedleFqPoseidonFSRngGadget = DensityOptimizedPoseidonQuinticSBoxFSRngGadget<
    TweedleFq,
    TweedleFqPoseidonParameters,
    TweedleFqDensityOptimizedPoseidonParameters
>;

#[cfg(test)]
mod test {
    use crate::constraints::test::{test_native_result, fs_rng_consistency_test};
    use crate::poseidon::{TweedleFrPoseidonFSRng, TweedleFqPoseidonFSRng};
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_tweedle_dum() {
        use algebra::curves::tweedle::dum::DumJacobian as TweedleDum;
        use super::*;

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        for seed in vec![None, Some(b"TEST_SEED".to_vec())] {
            for i in 1..=5 {
                test_native_result::<TweedleDum, TweedleFrPoseidonFSRng, TweedleFrPoseidonFSRngGadget, _, 128>(rng, i, seed.clone());
            }
        }
        fs_rng_consistency_test::<TweedleDum, TweedleFrPoseidonFSRngGadget, _, 128>(rng);   
    }

    #[test]
    fn test_tweedle_dee() {
        use algebra::curves::tweedle::dee::DeeJacobian as TweedleDee;
        use super::*;

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        for seed in vec![None, Some(b"TEST_SEED".to_vec())] {
            for i in 1..=5 {
                test_native_result::<TweedleDee, TweedleFqPoseidonFSRng, TweedleFqPoseidonFSRngGadget, _, 128>(rng, i, seed.clone());
            }
        }
        fs_rng_consistency_test::<TweedleDee, TweedleFqPoseidonFSRngGadget, _, 128>(rng);
    }
}