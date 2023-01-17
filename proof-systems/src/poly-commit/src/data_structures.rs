use crate::{Rc, String, Vec};
pub use algebra::DensePolynomial as Polynomial;
use algebra::{
    serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError},
    Field, SemanticallyValid, ToBytes,
};
use rand_core::RngCore;
use std::{
    borrow::Borrow,
    fmt::Debug,
    io::{Error as IoError, ErrorKind, Read, Result as IoResult, Write},
    ops::{AddAssign, MulAssign, SubAssign},
};

/// Labels a `LabeledPolynomial` or a `LabeledCommitment`.
pub type PolynomialLabel = String;

/// Defines the minimal interface for public params for any polynomial
/// commitment scheme.
pub trait PCUniversalParams:
    Clone + Debug + CanonicalSerialize + CanonicalDeserialize + Eq + PartialEq
{
    /// Outputs the maximum degree supported by the committer key.
    fn max_degree(&self) -> usize;

    /// Returns the hash of `self` instance.
    fn get_hash(&self) -> &[u8];

    /// Copy other instance params into this. Used for testing purposes.
    fn copy_params(&mut self, other: &Self);
}

/// Defines the minimal interface of committer keys for any polynomial
/// commitment scheme.
pub trait PCCommitterKey:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize + SemanticallyValid
{
    /// Outputs the maximum degree supported by the universal parameters
    /// `Self` was derived from.
    fn max_degree(&self) -> usize;

    /// Outputs the maximum degree supported by the committer key.
    fn supported_degree(&self) -> usize;

    /// Returns the hash of `self` instance.
    fn get_hash(&self) -> &[u8];

    /// Randomize key for testing purpose
    fn randomize(&mut self);
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
    fn supported_degree(&self) -> usize;

    /// Returns the hash of `self` instance.
    fn get_hash(&self) -> &[u8];

    /// Randomize key for testing purpose
    fn randomize(&mut self);
}

/// Defines the minimal interface of prepared verifier keys for any polynomial
/// commitment scheme.
pub trait PCPreparedVerifierKey<Unprepared: PCVerifierKey> {
    /// prepare
    fn prepare(vk: &Unprepared) -> Self;
}

/// Defines the minimal interface of commitments for any polynomial
/// commitment scheme.
pub trait PCCommitment:
    Clone + CanonicalSerialize + CanonicalDeserialize + ToBytes + SemanticallyValid
{
    /// Outputs a non-hiding commitment to the zero polynomial.
    fn empty() -> Self;

    /// Does this commitment have a degree bound?
    fn has_degree_bound(&self) -> bool;

    /// Randomize commiment values for testing purpose
    fn randomize(&mut self);
}

/// Defines the minimal interface of prepared commitments for any polynomial
/// commitment scheme.
pub trait PCPreparedCommitment<UNPREPARED: PCCommitment>: Clone {
    /// prepare
    fn prepare(comm: &UNPREPARED) -> Self;
}

/// Defines the minimal interface of commitment randomness for any polynomial
/// commitment scheme.
pub trait PCRandomness:
    Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize
{
    /// Outputs empty randomness that does not hide the commitment.
    fn empty(segments_count: usize) -> Self;

    /// Samples randomness for commitments;
    /// `num_queries` specifies the number of queries that the commitment will be opened at.
    /// `has_degree_bound` indicates that the corresponding commitment has an enforced
    /// strict degree bound.
    fn rand<R: RngCore>(num_queries: usize, has_degree_bound: bool, rng: &mut R) -> Self;
}

/// A polynomial along with information about its degree bound (if any), and the
/// maximum number of queries that will be made to it. This latter number determines
/// the amount of protection that will be provided to a commitment for this polynomial.
#[derive(Debug, Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct LabeledPolynomial<F: Field> {
    label: PolynomialLabel,
    polynomial: Rc<Polynomial<F>>,
    degree_bound: Option<usize>,
    hiding_bound: Option<usize>,
}

impl<'a, F: Field> std::ops::Deref for LabeledPolynomial<F> {
    type Target = Polynomial<F>;

    fn deref(&self) -> &Self::Target {
        &self.polynomial
    }
}

impl<'a, F: Field> LabeledPolynomial<F> {
    /// Construct a new labeled polynomial.
    pub fn new(
        label: PolynomialLabel,
        polynomial: Polynomial<F>,
        degree_bound: Option<usize>,
        hiding_bound: Option<usize>,
    ) -> Self {
        Self {
            label,
            polynomial: Rc::new(polynomial),
            degree_bound,
            hiding_bound,
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

    /// Retrieve the degree bound in `self`.
    pub fn degree_bound(&self) -> Option<usize> {
        self.degree_bound
    }

    /// Retrieve whether the polynomial in `self` should be hidden.
    pub fn is_hiding(&self) -> bool {
        self.hiding_bound.is_some()
    }

    /// Retrieve the hiding bound for the polynomial in `self`.
    pub fn hiding_bound(&self) -> Option<usize> {
        self.hiding_bound
    }
}

/// A commitment along with information about its degree bound (if any).
#[derive(Clone)]
pub struct LabeledCommitment<C: PCCommitment> {
    label: PolynomialLabel,
    commitment: C,
    degree_bound: Option<usize>,
}

impl<C: PCCommitment> LabeledCommitment<C> {
    /// Instantiate a new commitment_context.
    pub fn new(label: PolynomialLabel, commitment: C, degree_bound: Option<usize>) -> Self {
        Self {
            label,
            commitment,
            degree_bound,
        }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the commitment from `self`.
    pub fn commitment(&self) -> &C {
        &self.commitment
    }

    /// Retrieve the degree bound in `self`.
    pub fn degree_bound(&self) -> Option<usize> {
        self.degree_bound
    }

    /// Randomize commitment for test purpose
    pub fn randomize(&mut self) {
        self.commitment.randomize();
    }
}

impl<C: PCCommitment> SemanticallyValid for LabeledCommitment<C> {
    fn is_valid(&self) -> bool {
        self.commitment.is_valid()
    }
}

impl<C: PCCommitment> ToBytes for LabeledCommitment<C> {
    #[inline]
    fn write<W: Write>(&self, writer: W) -> IoResult<()> {
        self.commitment
            .serialize_without_metadata(writer)
            .map_err(|e| IoError::new(ErrorKind::Other, format! {"{:?}", e}))
    }
}

/// A labeled randomness.
#[derive(Clone, Debug, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct LabeledRandomness<Rand: PCRandomness> {
    label: PolynomialLabel,
    randomness: Rand,
}

impl<Rand: PCRandomness> LabeledRandomness<Rand> {
    /// Instantiate a new randomness_context.
    pub fn new(label: PolynomialLabel, randomness: Rand) -> Self {
        Self { label, randomness }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the commitment from `self`.
    pub fn randomness(&self) -> &Rand {
        &self.randomness
    }
}

/// A term in a linear combination.
#[derive(Hash, Ord, PartialOrd, Clone, Eq, PartialEq, Debug)]
pub enum LCTerm {
    /// The constant term representing `one`.
    One,
    /// Label for a polynomial.
    PolyLabel(String),
}

impl LCTerm {
    /// Returns `true` if `self == LCTerm::One`
    #[inline]
    pub fn is_one(&self) -> bool {
        if let LCTerm::One = self {
            true
        } else {
            false
        }
    }
}

impl From<PolynomialLabel> for LCTerm {
    fn from(other: PolynomialLabel) -> Self {
        Self::PolyLabel(other)
    }
}

impl<'a> From<&'a str> for LCTerm {
    fn from(other: &str) -> Self {
        Self::PolyLabel(other.into())
    }
}

impl std::convert::TryInto<PolynomialLabel> for LCTerm {
    type Error = ();
    fn try_into(self) -> Result<PolynomialLabel, ()> {
        match self {
            Self::One => Err(()),
            Self::PolyLabel(l) => Ok(l),
        }
    }
}

impl<'a> std::convert::TryInto<&'a PolynomialLabel> for &'a LCTerm {
    type Error = ();

    fn try_into(self) -> Result<&'a PolynomialLabel, ()> {
        match self {
            LCTerm::One => Err(()),
            LCTerm::PolyLabel(l) => Ok(l),
        }
    }
}

impl<B: Borrow<String>> PartialEq<B> for LCTerm {
    fn eq(&self, other: &B) -> bool {
        match self {
            Self::One => false,
            Self::PolyLabel(l) => l == other.borrow(),
        }
    }
}

/// A labeled linear combinations of polynomials.
#[derive(Clone, Debug)]
pub struct LinearCombination<F> {
    /// The label.
    pub label: String,
    /// The linear combination of `(coeff, poly_label)` pairs.
    pub terms: Vec<(F, LCTerm)>,
}

impl<F: Field> LinearCombination<F> {
    /// Construct an empty labeled linear combination.
    pub fn empty(label: impl Into<String>) -> Self {
        Self {
            label: label.into(),
            terms: Vec::new(),
        }
    }

    /// Construct a new labeled linear combination.
    /// with the terms specified in `term`.
    pub fn new(label: impl Into<String>, terms: Vec<(F, impl Into<LCTerm>)>) -> Self {
        let terms = terms.into_iter().map(|(c, t)| (c, t.into())).collect();
        Self {
            label: label.into(),
            terms,
        }
    }

    /// Returns the label of the linear combination.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Returns `true` if the linear combination has no terms.
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// Add a term to the linear combination.
    pub fn push(&mut self, term: (F, LCTerm)) -> &mut Self {
        self.terms.push(term);
        self
    }
}

impl<'a, F: Field> AddAssign<(F, &'a LinearCombination<F>)> for LinearCombination<F> {
    fn add_assign(&mut self, (coeff, other): (F, &'a LinearCombination<F>)) {
        self.terms
            .extend(other.terms.iter().map(|(c, t)| (coeff * c, t.clone())));
    }
}

impl<'a, F: Field> SubAssign<(F, &'a LinearCombination<F>)> for LinearCombination<F> {
    fn sub_assign(&mut self, (coeff, other): (F, &'a LinearCombination<F>)) {
        self.terms
            .extend(other.terms.iter().map(|(c, t)| (-coeff * c, t.clone())));
    }
}

impl<'a, F: Field> AddAssign<&'a LinearCombination<F>> for LinearCombination<F> {
    fn add_assign(&mut self, other: &'a LinearCombination<F>) {
        self.terms.extend(other.terms.iter().cloned());
    }
}

impl<'a, F: Field> SubAssign<&'a LinearCombination<F>> for LinearCombination<F> {
    fn sub_assign(&mut self, other: &'a LinearCombination<F>) {
        self.terms
            .extend(other.terms.iter().map(|(c, t)| (-*c, t.clone())));
    }
}

impl<F: Field> AddAssign<F> for LinearCombination<F> {
    fn add_assign(&mut self, coeff: F) {
        self.terms.push((coeff, LCTerm::One));
    }
}

impl<F: Field> SubAssign<F> for LinearCombination<F> {
    fn sub_assign(&mut self, coeff: F) {
        self.terms.push((-coeff, LCTerm::One));
    }
}

impl<F: Field> MulAssign<F> for LinearCombination<F> {
    fn mul_assign(&mut self, coeff: F) {
        self.terms.iter_mut().for_each(|(c, _)| *c *= coeff);
    }
}

impl<F: Field> std::ops::Deref for LinearCombination<F> {
    type Target = [(F, LCTerm)];

    fn deref(&self) -> &Self::Target {
        &self.terms
    }
}
