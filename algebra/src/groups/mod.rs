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

mod linear_combination;
pub use linear_combination::*;

mod group_vec;
pub use group_vec::*;

#[cfg(test)]
pub mod tests;

pub trait Group:
    'static
    + ToBytes
    + FromBytes
    + FromBytesChecked
    + SemanticallyValid
    + CanonicalSerialize
    + CanonicalDeserialize
    + Clone
    + Debug
    + Display
    + Default
    + Send
    + Sync
    + Eq
    + Hash
    + Neg<Output = Self>
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + AddAssign<Self>
    + SubAssign<Self>
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
