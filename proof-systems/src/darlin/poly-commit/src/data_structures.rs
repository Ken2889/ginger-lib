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
use crate::Error;
use crate::{Rc, String};
pub use algebra::DensePolynomial as Polynomial;
use algebra::{
    serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError},
    Field, Group, SemanticallyValid, ToBytes,
};
use std::{
    fmt::Debug,
    io::{Error as IoError, ErrorKind, Read, Result as IoResult, Write},
};

/// Labels a `LabeledPolynomial` or a `LabeledCommitment`.
pub type PolynomialLabel = String;

/// Labels the point(s) to which a `LabeledPolynomial` is queried at.
pub type PointLabel = String;

/// Defines the minimal interface for keys of any polynomial
/// commitment scheme.
pub trait PCKey:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize + SemanticallyValid
{
    /// Outputs the maximum degree supported by this key
    fn degree(&self) -> usize;

    /// Returns the hash of `self` instance.
    fn get_hash(&self) -> &[u8];

    /// Specialize the key for polynomials up to the given `degree`.
    fn trim(&self, degree: usize) -> Result<Self, Error>;
}

/// Defines the minimal interface of the verifier state from succinct
/// verify part.
/// This state is returned by the succinct verifier and contains everything
/// that is needed to complete verification.
pub trait PCVerifierState:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize
{
}

/// Defines the minimal interface of the verifier output from hard
/// verify part.
/// It can be used to output some intermediate calculation results which can
/// be useful for later postprocessing.
pub trait PCVerifierOutput: Clone + Debug + Eq + PartialEq {}

/// Defines the minimal interface for opening proofs for a polynomial commitment
pub trait PCProof:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize + SemanticallyValid
{
    /// Get degree of this proof.
    /// Allows to support some specific use cases, e.g. perform succinct verification of proofs using oversized keys.
    /// We might deprecate it in the future once we implement an efficient way to trim keys,
    /// thus enforcing proof verification with a vk the same size of the ck from which the proof was created.
    fn degree(&self) -> Result<usize, Error>;
}

/// Defines the minimal interface for batch evaluation proofs in the style
/// of Boneh et al [HaloInfinite], produced by `fn multi_point_multi_poly_open()`.
///
/// [HaloInfinite]: https://eprint.iacr.org/2020/1536
pub trait BDFGMultiPointProof<G: Group>:
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

impl<G: Group> ToBytes for LabeledCommitment<G> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        CanonicalSerialize::serialize(&self.commitment, &mut writer)
            .map_err(|e| IoError::new(ErrorKind::Other, format! {"{:?}", e}))
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
