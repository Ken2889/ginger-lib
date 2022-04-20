//! Trait for general (public, or "atomic") accumulation schemes [BCMS20](https://eprint.iacr.org/2020/499).
//! Comes with the aggregation/verification of "items", i.e. some data structure typically satisfying a
//! non-efficient predicate).  
//! The trait applies to mixed type accumulators as described in our Darlin Proof Tree document:
//! There, a (full) accumulator is a composite structure of dlog and inner sumcheck ("single") accumulators,
//! from both groups of the EC cycle (the "current", and the "collected" ones).
//! Although within recursion we do not separate accumulation strategy from the SNARK on protocol level,
//! we nevertheless serve this functionality for post processing outside the PCD.
use algebra::serialize::*;
use poly_commit::ipa_pc::{IPACurve, Proof};
use rand::RngCore;
use std::fmt::Debug;

pub mod composite;
pub mod dlog;
pub mod dual;
pub mod inner_sumcheck;
pub mod to_dual_field_vec;

pub type Error = Box<dyn std::error::Error>;

/// General struct of an aggregation proof. Typically, such proof stems from an
/// interactive oracle protocol (IOP) and a polynomial commitment scheme.
#[derive(Clone, Default, Debug, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulationProof<G: IPACurve> {
    /// Commitments to the polynomials produced by the prover.
    pub commitments: Vec<Vec<G>>,
    /// Evaluations of these polynomials.
    pub evaluations: Vec<G::ScalarField>,
    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: Proof<G>,
}

pub trait AccumulatorItem: Clone + Debug + CanonicalSerialize + CanonicalDeserialize {}

/// The `Accumulator` trait comes with the essential functions for proving
/// and verifying aggregation, as well as checking ("deciding") if an item
/// satisfies the predicate.
pub trait Accumulator {
    type ProverKey;
    type VerifierKey;
    type Proof;
    type Item: AccumulatorItem;
    type ExpandedItem;

    /// Expand an accumulator item, without checking the validity of its predicate.
    fn expand_item(
        vk: &Self::VerifierKey,
        accumulator: &Self::Item,
    ) -> Result<Self::ExpandedItem, Error>;

    /// Expand a list of accumulator items, without checking the validity of their predicates.
    fn expand_items(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
    ) -> Result<Vec<Self::ExpandedItem>, Error> {
        let result = accumulators
            .iter()
            .map(|acc| Self::expand_item(vk, acc))
            .collect::<Result<_, _>>();
        result
    }

    /// Check the validity of a single accumulator item.
    /// If successful, return the polynomial(s) behind the accumulator succinct descriptor.
    fn check_and_expand_item<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulator: &Self::Item,
        rng: &mut R,
    ) -> Result<Option<Self::ExpandedItem>, Error>;

    /// Check the validity of multiple accumulators.
    /// A default implementation is provided in terms of `check_item`.
    /// This implementation can be overridden so as to exploit
    fn check_and_expand_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<Option<Vec<Self::ExpandedItem>>, Error> {
        let mut output = Vec::with_capacity(accumulators.len());
        for acc in accumulators {
            let out = Self::check_and_expand_item(vk, acc, rng)?;
            if out.is_some() {
                output.push(out.unwrap())
            } else {
                return Ok(None);
            }
        }
        Ok(Some(output))
    }

    /// Decide whether an/the public accumulator/s are correct,
    /// i.e. whether they satisfy the non-efficient predicate.
    /// Typically involves non-succinct MSMs.
    fn check_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let output = Self::check_and_expand_items(vk, accumulators, rng)?;
        Ok(output.is_some())
    }

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
