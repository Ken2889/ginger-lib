use crate::error::Error;
use digest::{generic_array::GenericArray, Digest};
use rand::Rng;
use rand_chacha::ChaChaRng;
use rand_core::{RngCore, SeedableRng};
use std::{convert::TryInto, marker::PhantomData};
use super::*;

const EMPTY_INIT_STRING: &'static [u8] = b"EMPTY_SEED";
const GET_CHALLENGE_PREFIX: &'static [u8] = b"GET_CHALLENGE";

/// A `SeedableRng` that refreshes its seed by hashing together the previous seed
/// and the new seed material.
pub struct FiatShamirChaChaRng<D: Digest> {
    r: ChaChaRng,
    seed: GenericArray<u8, D::OutputSize>,
    #[doc(hidden)]
    digest: PhantomData<D>,
}

impl<D: Digest> FiatShamirChaChaRng<D> {

    /// Create a new `Self` by initializing with a fresh seed.
    #[inline]
    fn _from_seed(seed: Vec<u8>) -> Self {
        assert_eq!(D::output_size(), 32);

        // Hash the seed and use it as actual seed of the rng
        let seed = D::digest(&seed);
        let r_seed: [u8; 32] = seed.as_ref().try_into().unwrap();
        let r = ChaChaRng::from_seed(r_seed);

        Self {
            r,
            seed,
            digest: PhantomData,
        }
    }

    fn _record(&mut self, mut data: Vec<u8>) {
        data.extend_from_slice(&self.seed);
        self.seed = D::digest(data.as_slice());
        let seed: [u8; 32] = self.seed.as_ref().try_into().expect("failed to get [u32; 8]");
        self.r = ChaChaRng::from_seed(seed);
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

impl<D: Digest> Default for FiatShamirChaChaRng<D> {
    fn default() -> Self {
        Self::from_seed(EMPTY_INIT_STRING.to_vec()).unwrap()
    }
}

impl<D: Digest> FiatShamirRng for FiatShamirChaChaRng<D> {
    type State = Vec<u8>;

    #[inline]
    fn from_seed(seed: Vec<u8>) -> Result<Self, Error> {
        Ok(Self::_from_seed(seed))
    }

    /// Refresh `self.seed` with new material. Achieved by setting
    /// `self.seed = H(self.seed || new_seed)`.
    fn record<F: Field, R: Recordable<F>>(&mut self, data: R) -> Result<&mut Self, Error> {
        let mut bytes = Vec::new();
        data.serialize_without_metadata(&mut bytes).expect("failed to convert to bytes");
        self._record(bytes);
        Ok(self)
    }

    /// Get a new challenge
    fn get_challenge<const N: usize>(&mut self) -> Result<[bool; N], Error> {
        self._record(GET_CHALLENGE_PREFIX.to_vec());
        Ok(
            (0..N)
            .map(|_| self.gen::<bool>())
            .collect::<Vec<bool>>()
            .try_into()
            .unwrap()
        )
    }

    fn get_state(&self) -> Self::State {
        self.seed.as_ref().to_vec()
    }

    fn set_state(&mut self, state: Vec<u8>) -> Result<(), Error> { 
        if state.len() != D::output_size() {
            return Err(Error::BadFiatShamirInitialization("State length and digest output length are not the same".to_string()));
        }
        self.seed = GenericArray::<u8, D::OutputSize>::clone_from_slice(state.as_slice());
        let r_seed: [u8; 32] = state.try_into().unwrap(); // Cannot fail at this point
        self.r = ChaChaRng::from_seed(r_seed);
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use algebra::fields::tweedle::{Fr, Fq};
    use crate::test::{fs_rng_seed_builder_test, fs_rng_consistency_test};
    use super::FiatShamirChaChaRng;
    use blake2::Blake2s;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_blake2_chacha_fs_rng() {
        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        fs_rng_seed_builder_test::<Fr, FiatShamirChaChaRng<Blake2s>, 128>();
        fs_rng_seed_builder_test::<Fq, FiatShamirChaChaRng<Blake2s>, 128>();
        fs_rng_consistency_test::<FiatShamirChaChaRng<Blake2s>, Fr, Fq, _, 128>(rng);
        fs_rng_consistency_test::<FiatShamirChaChaRng<Blake2s>, Fq, Fr, _, 128>(rng);
    }
}