//! A sponge-like random oracle for Fiat-Shamir transform usage.

use algebra::{PrimeField, ToConstraintField, CanonicalSerialize, Field, EndoMulCurve, serialize_no_metadata};
use crate::error::Error;
use std::{fmt::Debug, convert::TryInto};

/// An implementation using the ChaCha20 based pseudo random number generator from
/// [rand_chacha](https://crates.io/crates/rand_chacha).
pub mod chacha20;

/// An implementation using Poseidon Sponge.
pub mod poseidon;

/// Traits definition for circuitizing FiatShamirRng. 
pub mod constraints;

/// Error types for FiatShamir
pub mod error;

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
pub trait Absorbable<F: Field>: ToConstraintField<F> + CanonicalSerialize {}

impl<F: Field, T: ToConstraintField<F> + CanonicalSerialize> Absorbable<F> for T {}

/// General trait for Fiat-Shamir transform, designed as a Sponge-based construction.
pub trait FiatShamirRng: Sized + Default {
    /// Internal State
    type State: Clone + Debug;

    /// Create a new `Self` by initializing its internal state with a fresh `seed`.
    fn from_seed(seed: Vec<u8>) -> Result<Self, Error>;

    /// Refresh the internal state with new material
    fn absorb<F: Field, A: Absorbable<F>>(&mut self, to_absorb: A) -> Result<&mut Self, Error>;

    /// Squeeze a new random field element, changing the internal state.
    fn squeeze<F: PrimeField>(&mut self) -> Result<F, Error> {
        Ok(self.squeeze_many(1)?[0])
    }

    /// Squeeze 'num' many random field elements, changing the internal state.
    /// Depending on the internal implementation, it might be more
    /// efficient than calling 'squeeze()' num times.
    fn squeeze_many<F: PrimeField>(&mut self, num: usize) -> Result<Vec<F>, Error>;

    /// Squeeze a new random field element having bit length of 128, changing the internal state.
    /// NOTE: We require the G: EndoMulCurve generic for backward compatibility reasons: we don't
    ///       want to duplicate code or filling it with ifs to discriminate among circuit-friendly
    ///       and non circuit-friendly Darlin primitive implementation. This generic will allow us to
    ///       squeeze a endo scalar in case of circuit friendly implementation and it will be simply
    ///       ignored by a non circuit friendly implementation.
    /// TODO: Can we do better ?
    fn squeeze_128_bits_challenge<G: EndoMulCurve>(&mut self) -> Result<G::ScalarField, Error> {
        Ok(self.squeeze_many_128_bits_challenges::<G>(1)?[0])
    }

    /// Squeeze 'num' many random field elements having bit length of 128, changing the internal state.
    /// Depending on the internal implementation, it might be more efficient than calling
    /// 'squeeze_128_bits_challenge' num times.
    fn squeeze_many_128_bits_challenges<G: EndoMulCurve>(&mut self, num: usize) -> Result<Vec<G::ScalarField>, Error>;

    /// Get the internal state in the form of an instance of `Self::Seed`.
    fn get_state(&self) -> Self::State;

    /// Set interal state according to the specified `new_seed`
    fn set_state(&mut self, new_state: Self::State);
}