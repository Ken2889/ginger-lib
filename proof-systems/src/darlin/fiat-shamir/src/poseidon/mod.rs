use crate::Recordable;
use algebra::{Field, FpParameters, PrimeField, ToConstraintField};
use primitives::PoseidonHash;
use primitives::{PoseidonParameters, SBox};

use super::{Error, FiatShamirRng};
use std::{convert::TryInto, marker::PhantomData};

/// Circuit implementation of this RNG
pub mod constraints;

/// Return true if F1 and F2 are of the same type, false otherwise
pub fn check_field_equals<F1: Field, F2: Field>() -> bool {
    std::any::TypeId::of::<F1>() == std::any::TypeId::of::<F2>()
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""), Debug(bound = ""))]
/// A Poseidon-based Fiat-shamir RNG, designed as a duplex Sponge construction.
pub struct PoseidonFSRng<
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
> {
    pub(crate) state: Vec<F>,
    pub(crate) pending_inputs: Vec<F>,
    pub(crate) pending_outputs: Vec<F>,
    _parameters: PhantomData<P>,
    _sbox: PhantomData<SB>,
}

impl<F, P, SB> PoseidonFSRng<F, P, SB>
where
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
{
    pub(crate) fn apply_permutations(&mut self) {
        // Process the inputs rate by rate
        if !self.pending_inputs.is_empty() {
            // calculate the number of cycles to process the input dividing in portions of rate elements
            let num_cycles = self.pending_inputs.len() / P::R;
            // check if the input is a multiple of the rate by calculating the remainder of the division
            // the remainder of dividing the input length by the rate can be 1 or 0 because we are assuming
            // that the rate is 2
            let rem = self.pending_inputs.len() % P::R;

            // index to process the input
            let mut input_idx = 0;
            // iterate of the portions of rate elements
            for _ in 0..num_cycles {
                // add the elements to the state vector. Add rate elements
                for j in 0..P::R {
                    self.state[j] += &self.pending_inputs[input_idx];
                    input_idx += 1;
                }

                // apply permutation after adding the input vector
                PoseidonHash::<F, P, SB>::poseidon_perm(&mut self.state);
            }

            // in case the input is not a multiple of the rate, process the remainder part padding zeros
            if rem != 0 {
                for j in 0..rem {
                    self.state[j] += &self.pending_inputs[input_idx];
                    input_idx += 1;
                }
                // apply permutation after adding the input vector
                PoseidonHash::<F, P, SB>::poseidon_perm(&mut self.state);
            }

            // Clear input buffer
            self.pending_inputs.clear();
        } else {
            // Apply permutation
            PoseidonHash::<F, P, SB>::poseidon_perm(&mut self.state);
        }

        // Push RATE many elements from the state into the output buffer
        self.pending_outputs
            .extend_from_slice(&self.state[..P::R]);
    }

    pub(crate) fn get_element(&mut self) -> F {
        if self.pending_outputs.is_empty() {
            self.apply_permutations();
        }
        self.pending_outputs.pop().unwrap()
    }

    // Get 'num_bits' from this sponge
    fn get_bits(&mut self, num_bits: usize) -> Result<Vec<bool>, Error> {
        if num_bits == 0 {
            return Err(Error::GetChallengeError(
                "No challenge to get !".to_string(),
            ));
        }

        // We return a certain amount of bits by getting field elements instead,
        // serialize them and return their bits.

        // Smallest number of field elements to retrieve to reach 'num_bits' is ceil(num_bits/FIELD_CAPACITY).
        // This is done to achieve uniform distribution over the output space, and it also
        // comes in handy as in the circuit we don't need to enforce range proofs for them.
        let usable_bits = F::Params::CAPACITY as usize;
        let num_elements = (num_bits + usable_bits - 1) / usable_bits;
        let mut src_elements = Vec::with_capacity(num_elements);

        // Apply as many permutations as needed to get the required number of field elements
        while src_elements.len() != num_elements {
            src_elements.push(self.get_element())
        }

        // Serialize field elements into bits and return them
        let mut dest_bits: Vec<bool> = Vec::with_capacity(num_bits);

        // discard leading zeros + 1 bit below modulus bits
        let skip = F::Params::MODULUS_BITS as usize - usable_bits;
        for elem in src_elements {
            let elem_bits = elem.write_bits();
            dest_bits.extend_from_slice(&elem_bits[skip..]);
        }
        Ok(dest_bits[..num_bits].to_vec())
    }
}

impl<F, P, SB> Default for PoseidonFSRng<F, P, SB>
where
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
{
    fn default() -> Self {
        let mut state = Vec::with_capacity(P::T);
        for i in 0..P::T {
            state.push(P::AFTER_ZERO_PERM[i]);
        }
        Self {
            state,
            pending_inputs: Vec::new(),
            pending_outputs: Vec::with_capacity(P::R),
            _parameters: PhantomData,
            _sbox: PhantomData,
        }
    }
}

impl<F, P, SB> FiatShamirRng for PoseidonFSRng<F, P, SB>
where
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
{
    type State = (Vec<F>, Vec<F>, Vec<F>);

    fn from_seed(seed: Vec<u8>) -> Result<Self, Error> {
        let mut new_inst = Self::default();

        // Update instance with seed elements
        new_inst
            .pending_inputs
            .append(&mut seed.to_field_elements().map_err(|e| {
                Error::BadFiatShamirInitialization(format!(
                    "Unable to convert seed to field elements: {:?}",
                    e
                ))
            })?);

        // Apply permutations
        new_inst.apply_permutations();

        // Clear outputs as we are only interested in keeping the state
        new_inst.pending_outputs.clear();

        // Return the new instance
        debug_assert!(new_inst.pending_inputs.is_empty());
        debug_assert!(new_inst.pending_outputs.is_empty());

        Ok(new_inst)
    }

    /// Record new data as part of this Fiat-Shamir transform
    fn record<RecordF: Field, R: Recordable<RecordF>>(
        &mut self,
        data: R,
    ) -> Result<&mut Self, Error> {
        // Get field elements
        let fes = data
            .to_field_elements()
            .map_err(|e| Error::RecordError(e.to_string()))?;

        if fes.is_empty() {
            return Err(Error::RecordError("Nothing to record !".to_string()));
        }

        // They refer to an old state, so we cannot use them anymore
        self.pending_outputs.clear();

        // Convert data to native field, if needed
        let mut elems = {
            // We are recording items belonging to native field
            if check_field_equals::<RecordF, F>() {
                // Safe casting, since we checked that the two types are the same
                // NOTE: If we don't want to use unsafe we can convert by serialization/deserialization
                //       but it's more expensive.
                unsafe { std::mem::transmute::<Vec<RecordF>, Vec<F>>(fes) }
            } else {
                // We want to record items belonging to non native field.
                // Collect all the bits
                let bits = fes
                    .iter()
                    .flat_map(|fe| fe.write_bits())
                    .collect::<Vec<_>>();

                // Read native field elements out of them in F::CAPACITY chunks
                bits.to_field_elements()
                    .map_err(|e| Error::RecordError(e.to_string()))?
            }
        };

        // Save new inputs to be processed
        self.pending_inputs.append(&mut elems);
        Ok(self)
    }

    fn get_challenge<const N: usize>(&mut self) -> Result<[bool; N], Error> {
        // In this case the get_many is more efficient
        Ok(self.get_many_challenges::<N>(1)?[0])
    }

    fn get_many_challenges<const N: usize>(&mut self, num: usize) -> Result<Vec<[bool; N]>, Error> {
        let bits = self.get_bits(num * N)?;
        debug_assert!(self.pending_inputs.is_empty());

        Ok(bits
            .chunks_exact(N)
            .map(|bit_chunk| bit_chunk.try_into().unwrap())
            .collect())
    }

    fn get_state(&self) -> Self::State {
        (
            self.state.clone(),
            self.pending_inputs.clone(),
            self.pending_outputs.clone(),
        )
    }

    fn set_state(&mut self, state: Self::State) -> Result<(), Error> {
        let (state, pending_inputs, pending_outputs) = state;
        if state.len() != P::T || pending_outputs.len() > P::R {
            return Err(Error::BadFiatShamirInitialization(
                "Attempt to set an invalid state".to_string(),
            ));
        }

        self.state = state;
        self.pending_inputs = pending_inputs;
        self.pending_outputs = pending_outputs;

        Ok(())
    }
}

#[cfg(feature = "tweedle")]
use {
    algebra::fields::tweedle::{Fq as TweedleFq, Fr as TweedleFr},
    primitives::crh::poseidon::parameters::{
        tweedle_dee::{TweedleFrPoseidonParameters, TweedleFrQuinticSbox},
        tweedle_dum::{TweedleFqPoseidonParameters, TweedleFqQuinticSbox},
    },
};

#[cfg(feature = "tweedle")]
pub type TweedleFrPoseidonFSRng =
    PoseidonFSRng<TweedleFr, TweedleFrPoseidonParameters, TweedleFrQuinticSbox>;

#[cfg(feature = "tweedle")]
pub type TweedleFqPoseidonFSRng =
    PoseidonFSRng<TweedleFq, TweedleFqPoseidonParameters, TweedleFqQuinticSbox>;

#[cfg(all(test, feature = "tweedle"))]
mod test {
    use super::*;
    use crate::test::{fs_rng_consistency_test, fs_rng_seed_builder_test};
    use algebra::fields::tweedle::{Fq as TweedleFq, Fr as TweedleFr};
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    fn test_permutation_with_poseidon_fs<F, P, SB, const N: usize>()
    where
        F: PrimeField,
        P: PoseidonParameters<Fr = F>,
        SB: SBox<Field = F, Parameters = P>,
    {
        assert!(P::R > 1);
        // Initialize Poseidon
        let mut fs_rng = PoseidonFSRng::<F, P, SB>::default();
        let mut prev = fs_rng.state.clone();

        // Get a challenge and trigger a permutation
        fs_rng.get_challenge::<N>().unwrap();
        let mut curr = fs_rng.state.clone();
        assert_ne!(prev, curr); // State has changed
        prev = curr;
        assert_eq!(fs_rng.pending_outputs.len(), P::R - 1);

        for i in 1..P::R {
            fs_rng.get_challenge::<N>().unwrap();
            curr = fs_rng.state.clone();
            // State shouldn't change as when we call get_challenge() we save
            // up to RATE elements from the state to be used for subsequent
            // get_challenge() calls
            assert_eq!(prev, curr);
            prev = curr;
            assert_eq!(fs_rng.pending_outputs.len(), P::R - (i + 1));
        }

        assert_eq!(fs_rng.pending_outputs.len(), 0);

        // When the buffered RATE outputs are over, a new permutation is triggered
        // when we ask for further challenges
        fs_rng.get_challenge::<N>().unwrap();
        curr = fs_rng.state.clone();
        assert_ne!(prev, curr);
        assert_eq!(fs_rng.pending_outputs.len(), P::R - 1);

        // However, when we record new data, pending outputs are cleared
        fs_rng.record::<F, _>("TEST_RECORD").unwrap();
        assert!(fs_rng.pending_outputs.is_empty());
        assert_eq!(fs_rng.pending_inputs.len(), 1);
    }

    #[test]
    fn test_poseidon_sponge_tweedle_fr() {
        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        fs_rng_seed_builder_test::<TweedleFr, TweedleFrPoseidonFSRng, 128>();
        fs_rng_seed_builder_test::<TweedleFq, TweedleFrPoseidonFSRng, 128>();
        fs_rng_consistency_test::<TweedleFrPoseidonFSRng, TweedleFr, TweedleFq, _, 128>(rng);
        fs_rng_consistency_test::<TweedleFrPoseidonFSRng, TweedleFq, TweedleFr, _, 128>(rng);
        test_permutation_with_poseidon_fs::<TweedleFr, TweedleFrPoseidonParameters, TweedleFrQuinticSbox, 128>();
    }

    #[test]
    fn test_poseidon_sponge_tweedle_fq() {
        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        fs_rng_seed_builder_test::<TweedleFq, TweedleFqPoseidonFSRng, 128>();
        fs_rng_seed_builder_test::<TweedleFr, TweedleFqPoseidonFSRng, 128>();
        fs_rng_consistency_test::<TweedleFqPoseidonFSRng, TweedleFq, TweedleFr, _, 128>(rng);
        fs_rng_consistency_test::<TweedleFqPoseidonFSRng, TweedleFr, TweedleFq, _, 128>(rng);
        test_permutation_with_poseidon_fs::<TweedleFq, TweedleFqPoseidonParameters, TweedleFqQuinticSbox, 128>();
    }
}
