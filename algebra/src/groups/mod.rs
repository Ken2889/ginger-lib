use crate::{
    bytes::{FromBytes, ToBytes},
    fields::{PrimeField, SquareRootField},
    UniformRand
};
use crate::{CanonicalDeserialize, CanonicalSerialize, FromBytesChecked, SemanticallyValid, ToConstraintField};

use std::{
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use num_traits::Zero;
use serde::*;

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
    + Serialize
    + for<'a> Deserialize<'a>
    + Clone
    + Debug
    + Display
    + Default
    + Send
    + Sync
    + Eq
    + Hash
    + UniformRand
    + Zero
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
    + ToConstraintField<<Self as Group>::BaseField>
{
    type BaseField: PrimeField + SquareRootField;
    type ScalarField: PrimeField;

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
