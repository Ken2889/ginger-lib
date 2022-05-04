//! Trait for general (public, or "atomic") accumulation schemes [BCMS20](https://eprint.iacr.org/2020/499).
//! Comes with the aggregation/verification of "items", i.e. some data structure typically satisfying a
//! non-efficient predicate).  
//! The trait applies to mixed type accumulators as described in our Darlin Proof Tree document:
//! There, a (full) accumulator is a composite structure of dlog and inner sumcheck ("single") accumulators,
//! from both groups of the EC cycle (the "current", and the "collected" ones).
//! Although within recursion we do not separate accumulation strategy from the SNARK on protocol level,
//! we nevertheless serve this functionality for post processing outside the PCD.
use algebra::serialize::*;
use algebra::{DensePolynomial, Group, ToConstraintField};
use rand::RngCore;
use std::fmt::Debug;

pub mod dlog;
pub mod dual;
pub mod inner_sumcheck;
pub mod t_dlog;
#[cfg(test)]
mod tests;

pub type Error = Box<dyn std::error::Error>;

/// The `Accumulator` trait comes with the essential functions for proving
/// and verifying aggregation, as well as checking ("deciding") if an item
/// satisfies the predicate.
pub trait Accumulator {
    type Group: Group;
    type ProverKey;
    type VerifierKey;
    type Proof;
    type Item: AccumulatorItem<Group = Self::Group>;

    /// Decide whether an/the public accumulator/s are correct,
    /// i.e. whether they satisfy the non-efficient predicate.
    /// Typically involves non-succinct MSMs.
    fn check_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error>;

    /// Amortization strategy for items as a separate argument.  
    /// Returns the new/"updated" item and a non-interactive
    /// proof of its correct aggregation.
    fn accumulate_items(
        ck: &Self::ProverKey,
        accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::Proof), Error>;

    /// Fully verifies a proof produced by accumulate_items() given the accumulators.
    /// Depending on the PC it may involve a non-succinct MSM.
    fn verify_accumulated_items<R: RngCore>(
        current_accumulator: &Self::Item,
        vk: &Self::VerifierKey,
        previous_accumulators: Vec<Self::Item>,
        proof: &Self::Proof,
        rng: &mut R,
    ) -> Result<bool, Error>;

    /// Define the trivial instance of accumulator item.
    /// Used for bootstrapping recursion.
    fn trivial_item(vk: &Self::VerifierKey) -> Result<Self::Item, Error>;

    /// Generate a random (but valid) instance of accumulator item for testing purposes.
    fn random_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error>;

    /// Generate a random, invalid instance of accumulator item for testing purposes.
    fn invalid_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error>;
}

pub trait AccumulatorItem:
    Clone
    + Debug
    + CanonicalSerialize
    + CanonicalDeserialize
    + ToConstraintField<<<Self as AccumulatorItem>::Group as Group>::ScalarField>
{
    type Group: Group;
}

pub struct NonNativeItem<'a, T: AccumulatorItem>(pub &'a T);

pub trait AsNonNativeItem<T: AccumulatorItem> {
    fn as_non_native(&self) -> NonNativeItem<T>;
}

impl<T: AccumulatorItem> AsNonNativeItem<T> for T {
    fn as_non_native(&self) -> NonNativeItem<T> {
        NonNativeItem(self)
    }
}

impl<T: AccumulatorItem> AsNonNativeItem<T> for &T {
    fn as_non_native(&self) -> NonNativeItem<T> {
        NonNativeItem(self)
    }
}

pub trait BatchableAccumulator {
    type Group: Group;
    type VerifierKey;
    type Item: AccumulatorItem<Group = Self::Group>;

    fn batch_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<
        (
            Self::Group,
            DensePolynomial<<Self::Group as Group>::ScalarField>,
        ),
        Error,
    >;
}
