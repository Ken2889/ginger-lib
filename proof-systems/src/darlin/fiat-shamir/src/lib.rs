//! A fs_rng-like random oracle for Fiat-Shamir transform usage.

use algebra::{ToConstraintField, CanonicalSerialize, Field, serialize_no_metadata};
use crate::error::Error;
use std::{fmt::Debug, convert::TryInto};

/// An implementation using the ChaCha20 based pseudo random number generator from
/// [rand_chacha](https://crates.io/crates/rand_chacha).
pub mod chacha20;

/// An implementation using Poseidon fs_rng.
pub mod poseidon;

/// Traits definition for circuitizing FiatShamirRng. 
pub mod constraints;

/// Error types for FiatShamir
pub mod error;

#[macro_use]
extern crate derivative;

/// A trait for serialization of [`FiatShamirRng`] seed material.
#[derive(Default)]
/// Encoding of seed material as discussed in [issue/22](https://github.com/HorizenLabs/poly-commit/issues/22).
/// Output type of the seed is a byte array.
pub struct FiatShamirRngSeed {
    // the number of seed elements.
    num_elements: u64,
    // the byte lengths of the seed elements.
    elements_len: Vec<u64>,
    // the concatenated byte sequence of elements.
    seed_bytes: Vec<u8>,
}

impl FiatShamirRngSeed {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_bytes<'a, T: 'a + CanonicalSerialize>(&mut self, elem: &'a T) -> Result<&mut Self, Error> {
        // Check we have not reached the maximum allowed seed size
        if self.num_elements == u64::MAX {
            return Err(Error::BadFiatShamirInitialization(format!(
                "Maximum seed length {} exceeded",
                u64::MAX
            )));
        }

        // Get elem bytes and check that they are not over the maximum allowed elem len
        let mut elem_bytes = serialize_no_metadata!(elem).map_err(|_| {
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

    pub fn finalize(self) -> Result<Vec<u8>, Error> 
    {
        serialize_no_metadata![self.num_elements, self.elements_len, self.seed_bytes]
            .map_err(|e| {
                Error::BadFiatShamirInitialization(format!("Unable to finalize seed: {:?}", e))
        })
    }
}

/// Thin wrapper around a type which is ToConstraintField + CanonicalSerialize
pub trait Recordable<F: Field>: ToConstraintField<F> + CanonicalSerialize {}

impl<F: Field, T: ToConstraintField<F> + CanonicalSerialize> Recordable<F> for T {}

/// General trait for Fiat-Shamir transform, designed as a fs_rng-based construction.
pub trait FiatShamirRng: Sized + Default {
    /// Internal State
    type State: Clone + Debug + Eq + PartialEq;

    /// Create a new `Self` by initializing its internal state with a fresh `seed`.
    fn from_seed(seed: Vec<u8>) -> Result<Self, Error>;

    /// Record new data as part of this Fiat-Shamir transform
    fn record<F: Field, R: Recordable<F>>(&mut self, data: R) -> Result<&mut Self, Error>;

    /// Get a new N bits challenge
    fn get_challenge<const N: usize>(&mut self) -> Result<[bool; N], Error>;

    /// Get 'num' many N bits challenges.
    /// It might be more efficient than calling 'get_challenge::<N>' num many times.
    fn get_many_challenges<const N: usize>(&mut self, num: usize) -> Result<Vec<[bool; N]>, Error> {
        (0..num).map(|_| self.get_challenge()).collect()
    }

    /// Get the internal state.
    fn get_state(&self) -> Self::State;

    /// Set the internal state.
    /// Return Error if the passed state is invalid.
    fn set_state(&mut self, state: Self::State) -> Result<(), Error>;

    /// Initialize a new instance from a given state.
    fn from_state(state: Self::State) -> Result<Self, Error> {
        let mut new = Self::default();
        new.set_state(state)?;
        Ok(new)
    }

    /// Reset internal state
    fn reset(&mut self) {
        *self = Self::default();
    }
}

#[cfg(test)]
pub(crate) mod test {
    use rand::{Rng, RngCore};
    use crate::{FiatShamirRngSeed, FiatShamirRng};
    use algebra::PrimeField;

    pub(crate) fn fs_rng_seed_builder_test<F: PrimeField, FS: FiatShamirRng, const N: usize>() {
        // Empty test
        {
            let mut rng1 = FS::from_seed(
                FiatShamirRngSeed::new().finalize().unwrap(),
            ).unwrap();
            let mut rng2 = FS::from_seed(
                FiatShamirRngSeed::new().finalize().unwrap(),
            ).unwrap();

            assert_eq!(rng1.get_state(), rng2.get_state());

            let a = rng1.get_challenge::<N>().unwrap();
            let b = rng2.get_challenge::<N>().unwrap();

            assert_eq!(a, b);
            assert_eq!(rng1.get_state(), rng2.get_state());

            rng1.record::<F, _>("ABSORBABLE_ELEM").unwrap();
            rng2.record::<F, _>("ABSORBABLE_ELEM").unwrap();

            assert_eq!(rng1.get_state(), rng2.get_state());

            let a = rng1.get_challenge::<N>().unwrap();
            let b = rng2.get_challenge::<N>().unwrap();

            assert_eq!(a, b);
            assert_eq!(rng1.get_state(), rng2.get_state());
        }

        // No cross protocol attacks possible
        {
            let fs_rng_seed = {
                let mut seed_builder = FiatShamirRngSeed::new();
                seed_builder.add_bytes(b"TEST_SEED").unwrap();
                seed_builder.finalize().unwrap()
            };

            let malicious_fs_rng_seed = {
                let mut seed_builder = FiatShamirRngSeed::new();
                seed_builder.add_bytes(b"TEST_").unwrap();
                seed_builder.add_bytes(b"SEED").unwrap();
                seed_builder.finalize().unwrap()
            };

            let mut fs_rng = FS::from_seed(fs_rng_seed).unwrap();
            let mut malicious_fs_rng = FS::from_seed(malicious_fs_rng_seed).unwrap();

            assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

            let a = fs_rng.get_challenge::<N>().unwrap();
            let b = malicious_fs_rng.get_challenge::<N>().unwrap();

            assert_ne!(a, b);
            assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

            fs_rng.record::<F, _>("ABSORBABLE_ELEM").unwrap();
            malicious_fs_rng.record::<F, _>("ABSORBABLE_ELEM").unwrap();

            assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

            let a = fs_rng.get_challenge::<N>().unwrap();
            let b = malicious_fs_rng.get_challenge::<N>().unwrap();

            assert_ne!(a, b);
            assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());
        }

        // set_state test
        {
            let fs_rng_seed = {
                let mut seed_builder = FiatShamirRngSeed::new();
                seed_builder.add_bytes(b"TEST_SEED").unwrap();
                seed_builder.finalize().unwrap()
            };
            let mut fs_rng = FS::from_seed(fs_rng_seed).unwrap();

            let mut fs_rng_copy = FS::default();
            fs_rng_copy.set_state(fs_rng.get_state()).unwrap();

            assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());

            fs_rng.record::<F, _>("ABSORBABLE_ELEM").unwrap();
            fs_rng_copy.record::<F, _>("ABSORBABLE_ELEM").unwrap();

            assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());

            let a = fs_rng.get_challenge::<N>().unwrap();
            let b = fs_rng_copy.get_challenge::<N>().unwrap();

            assert_eq!(a, b);
            assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());
        }
    }

    pub(crate) fn fs_rng_consistency_test<
        FS: FiatShamirRng,
        F1: PrimeField,
        F2: PrimeField,
        R: RngCore,
        const N: usize,
    >(rng: &mut R)
    {
        let mut fs_rng = FS::default();
    
        // record random F1 field elements and check everything is fine
        let to_record = (0..10).map(|_| F1::rand(rng)).collect::<Vec<_>>();
        fs_rng.record(to_record).unwrap();
    
        // record random F2 field elements and check everything is fine
        let to_record = (0..10).map(|_| F2::rand(rng)).collect::<Vec<_>>();
        fs_rng.record(to_record).unwrap();
    
        // record random bytes and check everything is fine
        let to_record = (0..100).map(|_| rng.gen()).collect::<Vec<u8>>();
        fs_rng.record::<F1, _>(to_record.as_slice()).unwrap();
    
        // Check that calling get_challenge::<N>() multiple times without recording
        // changes the output
        let out = fs_rng.get_challenge::<N>().unwrap();
        let mut prev = out;
        for _ in 0..100 {
            let curr = fs_rng.get_challenge::<N>().unwrap();
            assert!(prev != curr);
            prev = curr;
        }
    
        // Record field elements and check that get_challenge:
        // -  outputs the correct number of challenges all different from each other
        // -  outputs challenges different from the previous ones if more data has been recorded
        fs_rng.reset();
        let mut set = std::collections::HashSet::new();
        set.insert(fs_rng.get_challenge::<N>().unwrap());
        let random_fes = (0..10).map(|_| F1::rand(rng)).collect::<Vec<_>>();

        for i in 1..=10 {
            fs_rng.reset();
            let random_fes = random_fes[..i].to_vec();
            fs_rng.record(random_fes).unwrap();
    
            // Native get_many_challenges::<N> test
            let outs = fs_rng.get_many_challenges::<N>(i).unwrap();
            assert_eq!(i, outs.len());

            // Bits shouldn't be all 0 with overwhelming probability
            outs
                .iter()
                .for_each(|out_bits| { assert!(!out_bits.iter().all(|bit| !bit)); });

            // Bits shouldn't be all 1 with overwhelming probability
            outs
                .iter()
                .for_each(|out_bits| { assert!(!out_bits.iter().all(|&bit| bit)); });
    
            // HashSet::insert(val) returns false if val was already present, so to check
            // that all the elements output by the fs_rng are different, we assert insert()
            // returning always true
            outs.into_iter().for_each(|f| assert!(set.insert(f)));
        }
    }
}