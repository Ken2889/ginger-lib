use crate::{
    fields::{BitIterator, Field, SquareRootField},
    groups::Group,
    CanonicalDeserialize, CanonicalSerialize, Error, FromBytes, ToBytes,
};
use serde::{Deserialize, Serialize};
use std::{
    convert::{TryFrom, TryInto},
    fmt::Debug,
    hash::Hash,
    ops::{AddAssign, Mul, Neg}
};
use num_traits::One;

pub mod models;

#[cfg(feature = "tweedle")]
pub mod tweedle;

#[cfg(feature = "secp256k1")]
pub mod secp256k1;

#[cfg(feature = "ed25519")]
pub mod ed25519;

#[cfg(test)]
pub mod tests;

pub use self::models::*;

/// Projective representation of an elliptic curve point.
/// This trait t serves curve-specific functions not covered
/// by the Group trait, in particular representation-specific
/// (i.e. mixed-type) arithmetic functions, that usually are
/// significantly faster.
pub trait Curve:
    Group
    + Copy // TODO: Let's consider removing this
    + Serialize
    + for<'a> Deserialize<'a>
    + From<<Self as Curve>::AffineRep>
    + TryInto<<Self as Curve>::AffineRep, Error = Error>
{
    /// The finite field over which this curve is defined.
    type BaseField: Field + SquareRootField;

    /// The affine representation of points on this curve.
    type AffineRep: Sized
        + Sync
        + Copy
        + PartialEq
        + Debug
        + Hash
        + Serialize
        + for<'a> Deserialize<'a>
        + CanonicalSerialize
        + CanonicalDeserialize
        + ToBytes
        + FromBytes
        + Neg<Output = Self::AffineRep>
        + TryFrom<Self, Error = Error>;

    /// Convert, if possible, `self` to its affine equivalent.
    #[inline]
    fn into_affine(&self) -> Result<Self::AffineRep, Error> {
        TryInto::<Self::AffineRep>::try_into(*self)
    }


    /// Construct a `self` point from its affine representation.
    #[inline]
    fn from_affine<'a>(other: &'a Self::AffineRep) -> Self {
        Into::<Self>::into(*other)
    }

    /// Convert, if possible, a batch of `self` points to their affine equivalent.
    #[inline]
    fn batch_into_affine<'a>(vec_self: Vec<Self>) -> Result<Vec<Self::AffineRep>, Error> {
        vec_self
            .into_iter()
            .map(|projective| projective.into_affine())
            .collect::<Result<Vec<_>, _>>()
    }

    /// Construct `self` points from a batch of their affine representation.
    #[inline]
    fn batch_from_affine<'a>(vec_affine:Vec<Self::AffineRep>) -> Vec<Self> {
        vec_affine
            .iter()
            .map(|&affine| affine.into())
            .collect::<Vec<_>>()
    }

    /// Add an affine point `other` to `self`, using mixed addition formulas.
    fn add_affine(&self, other: &Self::AffineRep) -> Self;

    /// Add assign an affine point `other` to `self`, using mixed addition formulas.
    fn add_assign_affine(&mut self, other: &Self::AffineRep);

    /// Given a batch of vectors, collapses them into single-element vectors carrying
    /// their respective additive totals.   
    fn add_in_place_affine_many(to_add: &mut [Vec<Self::AffineRep>]);

    /// Multiply `self` by the scalar represented by `bits`. 
    fn mul_bits<S: AsRef<[u64]>>(&self, bits: BitIterator<S>) -> Self {
        if self.is_zero() {
            *self
        } else {
            Self::mul_bits_affine(&self.into_affine().unwrap(), bits)
        }
    }

    /// Multiply an affine point `affine` by the scalar represented by `bits`. 
    fn mul_bits_affine<'a, S: AsRef<[u64]>>(
        affine: &'a Self::AffineRep,
        bits: BitIterator<S>,
    ) -> Self;

    /// Multiply `self` by the cofactor.
    fn scale_by_cofactor(&self) -> Self;

    /// Multiply `self` by the inverse of the cofactor in `Self::ScalarField`.
    fn scale_by_cofactor_inv(&self) -> Self;

    /// Returns a fixed generator of unknown exponent.
    #[must_use]
    fn prime_subgroup_generator() -> Self;

    /// Checks that the current point is on curve and is in the
    /// prime order subgroup
    #[must_use]
    fn group_membership_test(&self) -> bool;

    /// Return true if this point is on the curve, false otherwise.
    fn is_on_curve(&self) -> bool;

    /// Return true if this point is in the correct prime order subgroup.
    /// It won't check that the point is on the curve.
    fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool;

    /// Attempts to construct a point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    fn get_point_from_x(x: Self::BaseField, greatest: bool) -> Option<Self>;

    /// Attempts to construct a point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `parity` is set will the odd y-coordinate be selected.
    fn get_point_from_x_and_parity(x: Self::BaseField, parity: bool) -> Option<Self>;
}

/// The `EndoMulCurve` trait for curves that have a non-trivial endomorphism
/// `Phi` of the form `Phi(x,y) = (zeta*x,y)`.
pub trait EndoMulCurve: Curve {

    /// The curve parameters relevant for the endomorphism.
    type Params: EndoMulParameters<BaseField = Self::BaseField, ScalarField = Self::ScalarField>;

    /// Apply `Phi`
    fn apply_endomorphism(&self) -> Self;

    /// Conversion of a bit sequence used in `endo_mul()` into its equivalent scalar
    fn endo_rep_to_scalar(bits: Vec<bool>) -> Result<Self::ScalarField, Error> {
        let mut a: Self::ScalarField = 2u64.into();
        let mut b: Self::ScalarField = 2u64.into();

        let one = Self::ScalarField::one();
        let one_neg = one.neg();

        let mut bits = bits;
        if bits.len() % 2 == 1 {
            bits.push(false);
        }

        if bits.len() > Self::Params::LAMBDA {
            Err("Endo mul bits length exceeds LAMBDA")?
        }

        for i in (0..(bits.len() / 2)).rev() {
            a.double_in_place();
            b.double_in_place();

            let s = if bits[i * 2] { &one } else { &one_neg };

            if bits[i * 2 + 1] {
                a.add_assign(s);
            } else {
                b.add_assign(s);
            }
        }

        Ok(a.mul(Self::Params::ENDO_SCALAR) + &b)
    }

    /// Endomorphism-based multiplication of a curve point with a scalar
    /// in little-endian endomorphism representation.
    fn endo_mul(&self, bits: Vec<bool>) -> Result<Self, Error> {
        let mut bits = bits;
        if bits.len() % 2 == 1 {
            bits.push(false);
        }

        if bits.len() > Self::Params::LAMBDA {
            Err("Endo mul bits length exceeds LAMBDA")?
        }

        if self.is_zero() {
            return Ok(*self);
        }

        let self_affine = self.into_affine()?;
        let self_affine_neg = self_affine.neg();

        let self_e = self.apply_endomorphism();
        let self_affine_e = self_e.into_affine().unwrap();

        let self_affine_e_neg = self_affine_e.neg();

        let mut acc = self_e;
        acc.add_assign_affine(&self_affine);
        acc.double_in_place();

        for i in (0..(bits.len() / 2)).rev() {
            let s = if bits[i * 2 + 1] {
                if bits[i * 2] {
                    &self_affine_e
                } else {
                    &self_affine_e_neg
                }
            } else {
                if bits[i * 2] {
                    &self_affine
                } else {
                    &self_affine_neg
                }
            };

            acc.double_in_place();
            acc.add_assign_affine(s);
        }

        Ok(acc)
    }
}