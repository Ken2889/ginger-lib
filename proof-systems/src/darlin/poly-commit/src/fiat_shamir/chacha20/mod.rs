use crate::error::Error;
use crate::Vec;
use algebra::{to_bytes, PrimeField, FromBytes, ToBytes, ToConstraintField};
use digest::{generic_array::GenericArray, Digest};
use rand::Rng;
use rand_chacha::ChaChaRng;
use rand_core::{RngCore, SeedableRng};
use std::{convert::TryInto, marker::PhantomData};
use super::*;

#[derive(Default)]
/// Encoding of seed material as discussed in [issue/22](https://github.com/HorizenLabs/poly-commit/issues/22).
/// Output type of the seed is a byte array.
pub struct FiatShamirChaChaRngSeed {
    // the number of seed elements.
    num_elements: u64,
    // the byte lengths of the seed elements.
    elements_len: Vec<u64>,
    // the concatenated byte sequence of elements.
    seed_bytes: Vec<u8>,
}

impl FiatShamirRngSeed for FiatShamirChaChaRngSeed {
    type FinalizedSeed = Vec<u8>;
    type Error = Error;

    fn new() -> Self {
        Self::default()
    }

    fn add_bytes<'a, T: 'a + CanonicalSerialize>(&mut self, elem: &'a T) -> Result<&mut Self, Self::Error> {
        // Check we have not reached the maximum allowed seed size
        if self.num_elements == u64::MAX {
            return Err(Error::BadFiatShamirInitialization(format!(
                "Maximum seed length {} exceeded",
                u64::MAX
            )));
        }

        // Get elem bytes and check that they are not over the maximum allowed elem len
        let mut elem_bytes = Vec::with_capacity(elem.serialized_size()); 
        elem.serialize_without_metadata(&mut elem_bytes).map_err(|_| {
            Error::BadFiatShamirInitialization("Unable to convert elem to bytes".to_owned())
        })?;
        let elem_bytes_len: u64 = elem_bytes.len().try_into().map_err(|_| {
            Error::BadFiatShamirInitialization(format!(
                "Max elem length exceeded. Max: {}",
                u64::MAX
            ))
        })?;

        // Update internal state
        self.num_elements += 1;
        self.elements_len.push(elem_bytes_len);
        self.seed_bytes.append(&mut elem_bytes);
        Ok(self)
    }

    fn add_field<F: Field>(&mut self, elem: &F) -> Result<&mut Self, Self::Error> {
        let fe_bytes = to_bytes!(elem).map_err(|_| {
            Error::BadFiatShamirInitialization("Unable to convert fe to bytes".to_owned())
        })?;

        self.add_bytes(&fe_bytes)
    }

    fn finalize(mut self) -> Self::FinalizedSeed {
        let mut final_seed = Vec::new();
        final_seed.append(&mut to_bytes!(self.num_elements).unwrap());
        final_seed.append(&mut to_bytes!(self.elements_len).unwrap());
        final_seed.append(&mut self.seed_bytes);
        final_seed
    }
}

/// A `SeedableRng` that refreshes its seed by hashing together the previous seed
/// and the new seed material.
pub struct FiatShamirChaChaRng<D: Digest> {
    r: ChaChaRng,
    seed: GenericArray<u8, D::OutputSize>,
    #[doc(hidden)]
    digest: PhantomData<D>,
}

impl<D: Digest> Default for FiatShamirChaChaRng<D> {
    /// WARNING: Not intended for normal usage. FiatShamir must be initialized with proper,
    /// protocol-binded values. Use `from_seed` function instead.
    fn default() -> Self {
        Self::from_seed(FiatShamirChaChaRngSeed::default().finalize())
    }
}

impl<D: Digest> RngCore for FiatShamirChaChaRng<D> {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.r.next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.r.next_u64()
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.r.fill_bytes(dest);
    }

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.r.fill_bytes(dest);
        Ok(())
    }
}

impl<D: Digest> FiatShamirRng for FiatShamirChaChaRng<D> {
    type State = GenericArray<u8, D::OutputSize>;
    type Seed = FiatShamirChaChaRngSeed;
    type Error = Error;

    /// Refresh `self.seed` with new material. Achieved by setting
    /// `self.seed = H(self.seed || new_seed)`.
    fn absorb<F: Field, A: ToConstraintField<F> + CanonicalSerialize>(&mut self, to_absorb: A) -> Result<&mut Self, Self::Error> {
        let mut bytes = Vec::new();
        to_absorb.serialize_without_metadata(&mut bytes).expect("failed to convert to bytes");
        bytes.extend_from_slice(&self.seed);
        self.seed = D::digest(&bytes);
        let seed: [u8; 32] = FromBytes::read(self.seed.as_ref()).expect("failed to get [u32; 8]");
        self.r = ChaChaRng::from_seed(seed);
        Ok(self)
    }

    /// Create a new `Self` by initializing with a fresh seed.
    #[inline]
    fn from_seed(seed: <Self::Seed as FiatShamirRngSeed>::FinalizedSeed) -> Self {
        assert_eq!(D::output_size(), 32);

        // Hash the seed and use it as actual seed of the rng
        let seed = D::digest(&seed);
        let r_seed: [u8; 32] = FromBytes::read(seed.as_ref()).unwrap();
        let r = ChaChaRng::from_seed(r_seed);

        Self {
            r,
            seed,
            digest: PhantomData,
        }
    }

    /// Get `self.seed`.
    #[inline]
    fn get_state(&self) -> &Self::State {
        &self.seed
    }

    /// Set `self.seed` to the specified value
    #[inline]
    fn set_state(&mut self, new_state: Self::State) {
        self.seed = new_state.clone();
        let r_seed: [u8; 32] = new_state.as_ref().try_into().unwrap(); // Cannot fail at run-time
        self.r = ChaChaRng::from_seed(r_seed);
    }

    /// Squeeze a new random field element, changing the internal state.
    fn squeeze<F: PrimeField>(&mut self) -> F {
        F::rand(self)
    }

    /// Squeeze a new random field element having bit length of 128, changing the internal state.
    fn squeeze_128_bits_challenge<F: PrimeField>(&mut self) -> F {
        self.gen_range(1u128..=u128::MAX).into()
    }
}