use crate::UniformRand;
use crate::{
    CanonicalDeserialize, CanonicalSerialize, FromBytesChecked, SemanticallyValid,
};
use std::{
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Neg, Add, AddAssign, Sub, SubAssign, Mul, MulAssign},
};

use crate::{
    bytes::{FromBytes, ToBytes},
    fields::PrimeField,
};
// use serde::{Deserialize, Serialize};

#[cfg(test)]
pub mod tests;

pub trait Group:
    'static
    + ToBytes
    + FromBytes
    + FromBytesChecked
    + SemanticallyValid
    // + Serialize
    // + for<'a> Deserialize<'a>
    + CanonicalSerialize
    + CanonicalDeserialize
    // + Copy
    + Clone
    + Debug
    + Display
    + Default
    + Send
    + Sync
    + Eq
    + Hash
    + UniformRand
    + Neg<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Mul<&'a <Self as Group>::ScalarField, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> MulAssign<&'a <Self as Group>::ScalarField>
{
    type ScalarField: PrimeField;

    /// Returns the additive identity.
    fn zero() -> Self;

    /// Returns `self == zero`.
    fn is_zero(&self) -> bool;

    /// Returns `self + self`.
    #[must_use]
    fn double(&self) -> Self {
        let mut copy = self.clone();
        copy.double_in_place();
        copy
    }

    /// Sets `self := self + self`.
    fn double_in_place(&mut self) -> &mut Self;
}


/// Generic struct of a formal linear combination
pub struct LinearCombination<G: Group>
{
    items: Vec<(G::ScalarField, G)>
}

impl<G: Group> LinearCombination<G>
{
    /// Consturcts general LC
    pub fn new(items: Vec<(G::ScalarField, G)>) -> Self {
        LinearCombination {
            items
        }
    }

    /// Add term to LC
    pub fn push(&mut self, coeff: G::ScalarField, item: G) {
        self.items.push((coeff, item))
    }

    /// Combine LC
    pub fn combine(&self) -> G {
        let mut combined = G::zero();
        for (coeff, item) in self.items.iter() {
            combined += &(item.clone() * coeff);
        }
        combined
    }
}