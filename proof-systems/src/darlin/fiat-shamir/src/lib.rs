//! A sponge-like random oracle for Fiat-Shamir transform usage.

use algebra::{PrimeField, ToConstraintField, CanonicalSerialize, Field, EndoMulCurve};
use crate::error::Error;
use std::fmt::Debug;

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
pub trait FiatShamirRngSeed
{
    /// Output type of the seed, to be consistent with the seed type accepted
    /// by the `from_seed` function of FiatShamirRng.
    type FinalizedSeed: Sized + Clone;

    /// Initialize this seed
    fn new() -> Self;

    /// Update this seed with a new element interpreted as a sequence of byte
    fn add_bytes<'a, T: 'a + CanonicalSerialize>(&mut self, elem: &'a T) -> Result<&mut Self, Error>;

    /// Update this seed with a new field element
    fn add_field<F: PrimeField>(&mut self, elem: &F) -> Result<&mut Self, Error>;

    /// Finalize this seed to the type needed by the corresponding FiatShamirRng impl
    fn finalize(self) -> Result<Self::FinalizedSeed, Error>;
}

/// Thin wrapper around a type which is ToConstraintField + CanonicalSerialize
pub trait Absorbable<F: Field>: ToConstraintField<F> + CanonicalSerialize {}

impl<F: Field, T: ToConstraintField<F> + CanonicalSerialize> Absorbable<F> for T {}

/// General trait for Fiat-Shamir transform, designed as a Sponge-based construction.
pub trait FiatShamirRng: Sized + Default {
    /// Internal State
    type State: Clone + Debug;

    /// Seed from which initializing this Rng
    type Seed: FiatShamirRngSeed<FinalizedSeed = Self::State>;

    /// Create a new `Self` by initializing its internal state with a fresh `seed`.
    fn from_seed(seed: <Self::Seed as FiatShamirRngSeed>::FinalizedSeed) -> Self;

    /// Refresh the internal state with new material
    fn absorb<F: Field, A: Absorbable<F>>(&mut self, to_absorb: A) -> Result<&mut Self, Error>;

    /// Squeeze a new random field element, changing the internal state.
    fn squeeze<F: PrimeField>(&mut self) -> F;

    /// Squeeze a new random field element having bit length of 128, changing the internal state.
    /// NOTE: We require the G: EndoMulCurve generic for backward compatibility reasons: we don't
    ///       want to duplicate code or filling it with ifs to discriminate among circuit-friendly
    ///       and non circuit-friendly Darlin primitive implementation. This generic will allow us to
    ///       squeeze a endo scalar in case of circuit friendly implementation and it will be simply
    ///       ignored by a non circuit friendly implementation.
    /// TODO: Can we do better ?
    fn squeeze_128_bits_challenge<G: EndoMulCurve>(&mut self) -> G::ScalarField;

    /// Get the internal state in the form of an instance of `Self::Seed`.
    fn get_state(&self) -> Self::State;

    /// Set interal state according to the specified `new_seed`
    fn set_state(&mut self, new_state: Self::State);
}