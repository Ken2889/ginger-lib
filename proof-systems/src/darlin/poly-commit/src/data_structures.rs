//!
//! Contains traits for key material and evaluation proofs:
//!  * for parameters and key material of the scheme: [`PCParameters`], [`PCVerifierKey`], [`PCCommitterKey`]
//!  * for commitments and their hiding randomness: [`PCCommitment`], [`PCRandomness`]
//!  * for a simple (single-polynomial single-point) opening proof: [`PCProof`]  
//!  * for the [HaloInfinite] "batch evaluation" proof: [`PCMultiPointProof`]
//!  * [`PCVerifierState`] as needed due to the verifier splitting.
//!
//! Additionally the auxiliary structures [`LabeledCommitment`], [`LabeledPolynomial`],
//! [`LabeledRandomness`] are provided for internal usage.
//!
//! [HaloInfinite]: https://eprint.iacr.org/2020/1536
use crate::{error::*, Rc, String};
pub use algebra::DensePolynomial as Polynomial;
use algebra::{
    serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError},
    Field, Group, SemanticallyValid,
};
use std::{
    fmt::Debug,
    io::{Read, Write},
};

/// Labels a `LabeledPolynomial` or a `LabeledCommitment`.
pub type PolynomialLabel = String;

/// Defines the minimal interface of committer keys for any polynomial
/// commitment scheme.
pub trait PCCommitterKey:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize + SemanticallyValid
{
    /// Outputs the maximum degree supported by the universal parameters
    /// `Self` was derived from.
    fn max_degree(&self) -> usize;

    /// Outputs the maximum degree supported by the committer key.
    fn segment_size(&self) -> usize;

    /// Returns the hash of `self` instance.
    fn get_hash(&self) -> &[u8];

    /// Returns key length
    fn get_key_len(&self) -> usize;
}

/// Defines the minimal interface of verifier keys for any polynomial
/// commitment scheme.
pub trait PCVerifierKey:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize + SemanticallyValid
{
    /// Outputs the maximum degree supported by the universal parameters
    /// `Self` was derived from.
    fn max_degree(&self) -> usize;

    /// Outputs the maximum degree supported by the verifier key.
    fn segment_size(&self) -> usize;

    /// Returns the hash of `self` instance.
    fn get_hash(&self) -> &[u8];
}

/// Defines the minimal interface for public params for any polynomial
/// commitment scheme.
pub trait PCParameters<G: Group>:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize
{
    /// The committer key for the scheme; used to commit to a polynomial and then
    /// open the commitment to produce an evaluation proof.
    type CommitterKey: PCCommitterKey;
    /// The verifier key for the scheme; used to check an evaluation proof.
    type VerifierKey: PCVerifierKey;
    /// The error type for the scheme.
    type Error: std::error::Error + From<Error>;

    /// Outputs the maximum degree supported by the committer key.
    fn max_degree(&self) -> usize;

    /// Returns the hash of `self` instance.
    fn get_hash(&self) -> &[u8];

    /// Specializes the public parameters for polynomials up to the given `supported_degree`
    /// and for enforcing degree bounds in the range `1..=supported_degree`.
    fn trim(
        &self,
        segment_size: usize,
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), Self::Error>;
}

/// Defines the minimal interface of the verifier state from succinct
/// verify part.
/// This state is returned by the succinct verifier and contains everything
/// that is needed to complete verification.
pub trait PCVerifierState: Clone + Debug + Eq + PartialEq {}

/// Defines the minimal interface for opening proofs for a polynomial commitment
pub trait PCProof:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize + SemanticallyValid
{
    /// Return length of committer key
    fn get_key_len(&self) -> usize;
}

/// Defines the minimal interface for batch evaluation proofs in the style
/// of Boneh et al [HaloInfinite], produced by `fn multi_point_multi_poly_open()`.
///
/// [HaloInfinite]: https://eprint.iacr.org/2020/1536
pub trait PCMultiPointProof<G: Group>:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize + SemanticallyValid
{
    /// Commitment
    type Commitment;

    /// simple proof type
    type Proof: PCProof;

    /// Build new multi point proof from simple proof and commitment to h(X) polynomial
    fn new(proof: Self::Proof, h_commitment: Self::Commitment) -> Self;

    /// Outputs underlying simple proof
    fn get_proof(&self) -> &Self::Proof;

    /// Outputs the commitment to the multi-point multi-poly combination `h(X)`
    fn get_h_commitment(&self) -> &Self::Commitment;
}

/// A polynomial plus its `label` for reference.
#[derive(Debug, Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct LabeledPolynomial<F: Field> {
    label: PolynomialLabel,
    polynomial: Rc<Polynomial<F>>,
    is_hiding: bool,
}

impl<'a, F: Field> std::ops::Deref for LabeledPolynomial<F> {
    type Target = Polynomial<F>;

    fn deref(&self) -> &Self::Target {
        &self.polynomial
    }
}

impl<'a, F: Field> LabeledPolynomial<F> {
    /// Construct a new labeled polynomial.
    pub fn new(label: PolynomialLabel, polynomial: Polynomial<F>, is_hiding: bool) -> Self {
        Self {
            label,
            polynomial: Rc::new(polynomial),
            is_hiding,
        }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the polynomial from `self`.
    pub fn polynomial(&self) -> &Polynomial<F> {
        &self.polynomial
    }

    /// Evaluate the polynomial in `self`.
    pub fn evaluate(&self, point: F) -> F {
        self.polynomial.evaluate(point)
    }

    /// Retrieve whether the polynomial in `self` should be hidden.
    pub fn is_hiding(&self) -> bool {
        self.is_hiding
    }
}

/// A commitment plus its label, needed for reference.
#[derive(Clone)]
pub struct LabeledCommitment<G: Group> {
    label: PolynomialLabel,
    commitment: G,
}

impl<G: Group> LabeledCommitment<G> {
    /// Instantiate a new commitment_context.
    pub fn new(label: PolynomialLabel, commitment: G) -> Self {
        Self { label, commitment }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the commitment from `self`.
    pub fn commitment(&self) -> &G {
        &self.commitment
    }
}

impl<G: Group> SemanticallyValid for LabeledCommitment<G> {
    fn is_valid(&self) -> bool {
        self.commitment.is_valid()
    }
}

/// Likewise, the commitment randomnesses of a labeled polynomial.
#[derive(Clone, Debug, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct LabeledRandomness<G: Group> {
    label: PolynomialLabel,
    randomness: G,
}

impl<G: Group> LabeledRandomness<G> {
    /// Instantiate a new randomness_context.
    pub fn new(label: PolynomialLabel, randomness: G) -> Self {
        Self { label, randomness }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the commitment from `self`.
    pub fn randomness(&self) -> &G {
        &self.randomness
    }
}
