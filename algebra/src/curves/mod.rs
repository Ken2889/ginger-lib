use crate::{
    Error,
    groups::Group,
    fields::{Field, SquareRootField, PrimeField, BitIterator},
    UniformRand,
    CanonicalSerialize, CanonicalDeserialize, ToBytes, FromBytes
};
use serde::{Deserialize, Serialize};
use std::{
    fmt::Debug,
    hash::Hash,
    convert::{TryFrom, TryInto},
};

pub mod models;

#[cfg(feature = "tweedle")]
pub mod tweedle;

#[cfg(feature = "secp256k1")]
pub mod secp256k1;

#[cfg(test)]
pub mod tests;

pub use self::models::*;

pub trait Curve:
    Group
    + Copy
    + Serialize
    + for<'a> Deserialize<'a>
    + UniformRand
    + From<<Self as Curve>::AffineRep>
    + TryInto<<Self as Curve>::AffineRep, Error = Error>
{
    type BaseField: Field + SquareRootField;
    type AffineRep: Sized + Sync + Copy + PartialEq + Debug + Hash + CanonicalSerialize + CanonicalDeserialize + ToBytes + FromBytes + TryFrom<Self, Error = Error>;

    #[inline]
    fn into_affine(&self) -> Result<Self::AffineRep, Error> {
        TryInto::<Self::AffineRep>::try_into(*self)
    }

    #[inline]
    fn from_affine<'a>(other: &'a Self::AffineRep) -> Self {
        Into::<Self>::into(*other)
    }

    fn batch_from_affine<'a>(vec_affine: &'a [Self::AffineRep]) -> Vec<Self>
    {
        vec_affine.iter().map(|&affine| affine.into()).collect::<Vec<_>>()
    }

    fn batch_into_affine<'a>(vec_self: &'a [Self]) -> Result<Vec<Self::AffineRep>, Error>
    {
        vec_self.iter().map(|&projective| projective.into_affine()).collect::<Result<Vec<_>, _>>()
    }

    fn add_affine<'a>(&self, other: &'a Self::AffineRep) -> Self;

    fn add_affine_assign<'a>(&mut self, other: &'a Self::AffineRep);

    // TODO: move to group trait?
    fn mul_bits<S: AsRef<[u64]>>(&self, bits: BitIterator<S>) -> Self;

    fn mul_bits_affine<'a, S: AsRef<[u64]>>(affine: &'a Self::AffineRep, bits: BitIterator<S>) -> Self;

    fn scale_by_cofactor(&self) -> Self;

    fn scale_by_cofactor_inv(&self) -> Self;

    fn is_normalized(&self) -> bool;

    fn normalize(&self) -> Self;

    fn normalize_assign(&mut self);

    fn batch_normalization(v: &mut [Self]);

    fn batch_normalization_into_affine(mut v: Vec<Self>) -> Result<Vec<Self::AffineRep>, Error> {
        Self::batch_normalization(v.as_mut_slice());
        Self::batch_into_affine(v.as_slice())
    }
    /// Returns a fixed generator of unknown exponent.
    #[must_use]
    fn prime_subgroup_generator() -> Self;

    /// Checks that the current point is on curve and is in the
    /// prime order subgroup
    #[must_use]
    fn group_membership_test(&self) -> bool;

    fn is_on_curve(&self) -> bool;

    fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool;

    fn get_point_from_x(x: Self::BaseField, greatest: bool) -> Option<Self>;

    fn get_point_from_x_and_parity(x: Self::BaseField, parity: bool) -> Option<Self>;

    fn from_random_bytes(bytes: &[u8]) -> Option<Self>;

    // TODO: check if used
    fn recommended_wnaf_for_scalar(scalar: <Self::ScalarField as PrimeField>::BigInt) -> usize;

    // TODO: check if used
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize;

    // TODO: check naming
    fn sum_buckets_affine(to_add: &mut [Vec<Self::AffineRep>]);
}

pub trait EndoMulCurve: Curve {
    /// Apply `Phi`
    fn apply_endomorphism(&self) -> Self;

    /// Conversion of a bit sequence used in `endo_mul()` into its equivalent
    /// scalar
    fn endo_rep_to_scalar(bits: Vec<bool>) -> Result<Self::ScalarField, Error>;

    /// Endomorphism-based multiplication of `&self` with `bits`, a little-endian
    /// endomorphism representation.
    fn endo_mul(&self, bits: Vec<bool>) -> Result<Self, Error>;
}
