//! A crate for polynomial commitment schemes.
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public, variant_size_differences)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_mut)]
#![deny(missing_docs)]
#![deny(unused_imports)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]
#![allow(
    clippy::upper_case_acronyms,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::try_err,
    clippy::map_collect_result_unit,
    clippy::not_unsafe_ptr_arg_deref,
    clippy::suspicious_op_assign_impl,
    clippy::assertions_on_constants
)]

#[macro_use]
extern crate derivative;
#[macro_use]
extern crate bench_utils;

pub use algebra::fft::DensePolynomial as Polynomial;
use algebra::{serialize::*, Field, SemanticallyValid};
use rand_core::RngCore;

/// Implements a Fiat-Shamir based Rng that allows one to incrementally update
/// the seed based on new messages in the proof transcript.
pub mod rng;

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
    iter::FromIterator,
    rc::Rc,
    string::{String, ToString},
    vec::Vec,
};

/// Data structures used by a polynomial commitment scheme.
pub mod data_structures;
pub use data_structures::*;

/// Errors pertaining to query sets.
pub mod error;
pub use error::*;

use crate::rng::FiatShamirRng;

/// A random number generator that bypasses some limitations of the Rust borrow
/// checker.
pub mod optional_rng;

/// A polynomial commitment scheme based on the hardness of the
/// discrete logarithm problem in prime-order groups.
/// The construction is detailed in [[BCMS20]][pcdas].
///
/// [pcdas]: https://eprint.iacr.org/2020/499
pub mod ipa_pc;

/// `QuerySet` is the set of queries that are to be made to a set of labeled polynomials/equations
/// `p` that have previously been committed to. Each element of a `QuerySet` is a pair of
/// `(label, (point_label, point))`, where `label` is the label of a polynomial in `p`,
/// `point_label` is the label for the point (e.g., "beta"), and  and `point` is the field element
/// that `p[label]` is to be queried at.
pub type QuerySet<'a, F> = BTreeSet<(String, (String, F))>;

/// `Evaluations` is the result of querying a set of labeled polynomials or equations
/// `p` at a `QuerySet` `Q`. It maps each element of `Q` to the resulting evaluation.
/// That is, if `(label, query)` is an element of `Q`, then `evaluation.get((label, query))`
/// should equal `p[label].evaluate(query)`.
pub type Evaluations<'a, F> = BTreeMap<(String, F), F>;

/// A proof of satisfaction of linear combinations.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatchLCProof<F: Field, PC: PolynomialCommitment<F>> {
    /// Evaluation proof.
    pub proof: PC::BatchProof,
    /// Evaluations required to verify the proof.
    pub evals: Option<Vec<F>>,
}

impl<F: Field, PC: PolynomialCommitment<F>> SemanticallyValid for BatchLCProof<F, PC> {
    fn is_valid(&self) -> bool {
        self.proof.is_valid()
            && if self.evals.is_some() {
                self.evals.as_ref().unwrap().is_valid()
            } else {
                true
            }
    }
}

/// Describes the interface for a polynomial commitment scheme that allows
/// a sender to commit to multiple polynomials and later provide a succinct proof
/// of evaluation for the corresponding commitments at a query set `Q`, while
/// enforcing per-polynomial degree bounds.
pub trait PolynomialCommitment<F: Field>: Sized {
    /// The universal parameters for the commitment scheme. These are "trimmed"
    /// down to `Self::CommitterKey` and `Self::VerifierKey` by `Self::trim`.
    type UniversalParams: PCUniversalParams;
    /// The committer key for the scheme; used to commit to a polynomial and then
    /// open the commitment to produce an evaluation proof.
    type CommitterKey: PCCommitterKey;
    /// The verifier key for the scheme; used to check an evaluation proof.
    type VerifierKey: PCVerifierKey;
    /// The prepared verifier key for the scheme; used to check an evaluation proof.
    type PreparedVerifierKey: PCPreparedVerifierKey<Self::VerifierKey> + Clone;
    /// The commitment to a polynomial.
    type Commitment: PCCommitment + Default + Debug + Eq + PartialEq;
    /// The prepared commitment to a polynomial.
    type PreparedCommitment: PCPreparedCommitment<Self::Commitment>;
    /// The commitment randomness.
    type Randomness: PCRandomness;
    /// The evaluation proof for a single point.
    type Proof: Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize;
    /// The evaluation proof for a query set.
    type BatchProof: Clone
        + Debug
        + Eq
        + PartialEq
        + CanonicalSerialize
        + CanonicalDeserialize
        + SemanticallyValid;
    /// The error type for the scheme.
    type Error: std::error::Error + From<Error>;
    /// Source of random data
    type RandomOracle: FiatShamirRng<Error = Self::Error>;
    /// Constructs public parameters when given as input the maximum degree `degree`
    /// for the polynomial commitment scheme.
    fn setup(max_degree: usize) -> Result<Self::UniversalParams, Self::Error>;

    /// Constructs public parameters when given as input the maximum degree `degree`
    /// for the polynomial commitment scheme from given seed
    fn setup_from_seed(
        max_degree: usize,
        seed: &[u8],
    ) -> Result<Self::UniversalParams, Self::Error>;

    /// Specializes the public parameters for polynomials up to the given `supported_degree`
    /// and for enforcing degree bounds in the range `1..=supported_degree`.
    fn trim(
        pp: &Self::UniversalParams,
        supported_degree: usize,
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), Self::Error>;

    /// Outputs a commitments to `polynomials`. If `polynomials[i].is_hiding()`,
    /// then the `i`-th commitment is hiding up to `polynomials.hiding_bound()` queries.
    /// `rng` should not be `None` if `polynomials[i].is_hiding() == true` for any `i`.
    ///
    /// If for some `i`, `polynomials[i].is_hiding() == false`, then the
    /// corresponding randomness is `Self::Randomness::empty()`.
    ///
    /// If for some `i`, `polynomials[i].degree_bound().is_some()`, then that
    /// polynomial will have the corresponding degree bound enforced.
    fn commit<'a>(
        ck: &Self::CommitterKey,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<
        (
            Vec<LabeledCommitment<Self::Commitment>>,
            Vec<LabeledRandomness<Self::Randomness>>,
        ),
        Self::Error,
    >;

    /// Single point multi poly open:
    /// On input a list of labeled polynomials and a query point, `open` outputs a proof of evaluation
    /// of the polynomials at the query point.
    /// For now it is just a wrapper for the low-level function `open_individual_opening_challenges()`
    /// and hence assumes that the statement of the opening proof (i.e. the commitments, the query point,
    /// and the evaluations) are bound to the state of the Fiat-Shamir rng.
    fn open<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: F,
        fs_rng: &mut Self::RandomOracle,
        rands: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        Self::open_individual_opening_challenges(
            ck,
            labeled_polynomials,
            commitments,
            point,
            fs_rng,
            rands,
            rng,
        )
    }

    /// Multi point multi poly open:
    /// On input a list of labeled polynomials and a query set, `open` outputs a proof of evaluation
    /// of the polynomials at the points in the query set.
    /// For now it is just a wrapper for the low-level function `open_individual_opening_challenges()`
    /// and hence assumes that the statement of the opening proof (i.e. the commitments, the query set,
    /// and the evaluations) are bound to the state of the Fiat-Shamir rng.
    /// TODO: rename this function
    fn batch_open<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        fs_rng: &mut Self::RandomOracle,
        rands: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::BatchProof, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        Self::batch_open_individual_opening_challenges(
            ck,
            labeled_polynomials,
            commitments,
            query_set,
            fs_rng,
            rands,
            rng,
        )
    }

    /// Single point multi poly verify:
    /// Verifies that `values` are the evaluations at `point` of the polynomials
    /// committed inside `commitments`.
    fn check<'a>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: F,
        values: impl IntoIterator<Item = F>,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error>
    where
        Self::Commitment: 'a,
    {
        // as in open(), setup Fiat-Shamir rng, etc.
        Self::check_individual_opening_challenges(vk, commitments, point, values, proof, fs_rng)
    }

    /// Multi point multi poly verify:
    /// Checks that `values` are the true evaluations at `query_set` of the polynomials
    /// committed in `labeled_commitments`.
    /// TODO: rename this function
    fn batch_check<'a>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        evaluations: &Evaluations<F>,
        proof: &Self::BatchProof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error>
    where
        Self::Commitment: 'a,
    {
        Self::batch_check_individual_opening_challenges(
            vk,
            commitments,
            query_set,
            evaluations,
            proof,
            fs_rng,
        )
    }

    /// Multi point multi LC open:
    /// On input a list of polynomials, linear combinations of those polynomials,
    /// and a query set, `open_combination` outputs a proof of evaluation of
    /// the combinations at the points in the query set.
    /// For now it is just a wrapper for the low-level function `open_combinations_individual_opening_challenges()`
    /// and hence assumes that the statement of the opening proof (i.e. the LCs, the query set,
    /// and the evaluations) are bound to the state of the Fiat-Shamir rng.
    fn open_combinations<'a>(
        ck: &Self::CommitterKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        fs_rng: &mut Self::RandomOracle,
        rands: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<BatchLCProof<F, Self>, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        Self::open_combinations_individual_opening_challenges(
            ck,
            linear_combinations,
            polynomials,
            commitments,
            query_set,
            fs_rng,
            rands,
            rng,
        )
    }

    /// Multi point multi LC verify.
    /// Checks that `evaluations` are the true evaluations at `query_set` of the
    /// linear combinations of polynomials committed in `commitments`.
    fn check_combinations<'a>(
        vk: &Self::VerifierKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        eqn_query_set: &QuerySet<F>,
        eqn_evaluations: &Evaluations<F>,
        proof: &BatchLCProof<F, Self>,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error>
    where
        Self::Commitment: 'a,
    {
        Self::check_combinations_individual_opening_challenges(
            vk,
            linear_combinations,
            commitments,
            eqn_query_set,
            eqn_evaluations,
            proof,
            fs_rng,
        )
    }

    /// Single point multi poly open, allowing the random oracle to be passed from
    /// 'outside' to the function.
    /// CAUTION: This is a low-level function to be handled carefully, typically
    /// presuming that commitments and query_set is already bound to the internal
    /// state of the Fiat-Shamir rng.
    /// TODO: rename this function
    fn open_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: F,
        fs_rng: &mut Self::RandomOracle,
        rands: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        // `rng` if needed for blinding
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a;

    /// Multi point multi poly open, allowing the random oracle to be passed from
    /// 'outside' to the function.
    /// CAUTION: This is a low-level function to be handled carefully, typically
    /// presuming that commitments and query_set is already bound to the internal
    /// state of the Fiat-Shamir rng.
    /// TODO: rename this function
    fn batch_open_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        fs_rng: &mut Self::RandomOracle,
        rands: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::BatchProof, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a;

    /// Single point multi poly verify, with random oracle passed from 'outside'.
    /// CAUTION: This is a low-level function to be handled carefully, typically
    /// presuming that commitments and query_set is already bound to the internal
    /// state of the Fiat-Shamir rng.
    /// TODO: rename this function
    fn check_individual_opening_challenges<'a>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: F,
        values: impl IntoIterator<Item = F>,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error>
    where
        Self::Commitment: 'a;

    /// Multi point multi poly verify, with random oracle passed from 'outside'.
    /// CAUTION: This is a low-level function to be handled carefully, typically
    /// presuming that commitments and query_set is already bound to the internal
    /// state of the Fiat-Shamir rng.
    /// TODO: rename this function
    fn batch_check_individual_opening_challenges<'a>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        evaluations: &Evaluations<F>,
        proof: &Self::BatchProof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error>
    where
        Self::Commitment: 'a;

    /// Default implementation of Multi point multi LC open, with random oracle passed from 'outside'.
    /// Evaluates each of the (non-trivial) LC-polynomials at each of the query point the LC is queried.
    /// CAUTION: This is a low-level function to be handled with carefully, presuming that
    /// 1) the commitments
    /// 2) their LC's, and
    /// 3) the query set as well as the evaluations
    /// are already bound to the internal state of the Fiat-Shamir rng.
    // TODO: rename this function
    fn open_combinations_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<F>,
        fs_rng: &mut Self::RandomOracle,
        rands: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<BatchLCProof<F, Self>, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        let linear_combinations: Vec<_> = linear_combinations.into_iter().collect();
        let polynomials: Vec<_> = polynomials.into_iter().collect();
        let poly_query_set =
            lc_query_set_to_poly_query_set(linear_combinations.iter().copied(), query_set);
        let poly_evals = evaluate_query_set(polynomials.iter().copied(), &poly_query_set);
        let proof = Self::batch_open_individual_opening_challenges(
            ck,
            polynomials,
            commitments,
            &poly_query_set,
            fs_rng,
            rands,
            rng,
        )?;
        Ok(BatchLCProof {
            proof,
            evals: Some(poly_evals.values().copied().collect()),
        })
    }

    /// Default implementation of Multi point multi LC verify, with random oracle passed from 'outside'.
    /// Evaluates each of the (non-trivial) LC-polynomials at the query point.
    /// CAUTION: This is a low-level function to be handled carefully, typically
    /// presuming that commitments and query_set is already bound to the internal
    /// state of the Fiat-Shamir rng.
    /// TODO: rename this function
    fn check_combinations_individual_opening_challenges<'a>(
        vk: &Self::VerifierKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        eqn_query_set: &QuerySet<F>,
        eqn_evaluations: &Evaluations<F>,
        proof: &BatchLCProof<F, Self>,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error>
    where
        Self::Commitment: 'a,
    {
        let BatchLCProof { proof, evals } = proof;

        if !evals.is_some() {
            return Err(Error::IncorrectProof.into())
        }

        let lc_s = BTreeMap::from_iter(linear_combinations.into_iter().map(|lc| (lc.label(), lc)));

        let poly_query_set = lc_query_set_to_poly_query_set(lc_s.values().copied(), eqn_query_set);
        let poly_evals = Evaluations::from_iter(
            poly_query_set
                .iter()
                .map(|(_, point)| point)
                .cloned()
                .zip(evals.clone().unwrap()),
        );

        for &(ref lc_label, (_, point)) in eqn_query_set {
            if let Some(lc) = lc_s.get(lc_label) {
                let claimed_rhs = *eqn_evaluations.get(&(lc_label.clone(), point)).ok_or(
                    Error::MissingEvaluation {
                        label: lc_label.to_string(),
                    },
                )?;

                let mut actual_rhs = F::zero();

                for (coeff, label) in lc.iter() {
                    let eval = match label {
                        LCTerm::One => F::one(),
                        LCTerm::PolyLabel(l) => *poly_evals
                            .get(&(l.clone(), point))
                            .ok_or(Error::MissingEvaluation { label: l.clone() })?,
                    };

                    actual_rhs += &(*coeff * eval);
                }
                if claimed_rhs != actual_rhs {
                    eprintln!("Claimed evaluation of {} is incorrect", lc.label());
                    return Ok(false);
                }
            }
        }

        let pc_result = Self::batch_check_individual_opening_challenges(
            vk,
            commitments,
            &poly_query_set,
            &poly_evals,
            proof,
            fs_rng,
        )?;

        if !pc_result {
            eprintln!("Evaluation proofs failed to verify");
            return Ok(false);
        }

        Ok(true)
    }
}

/// Evaluate the given polynomials at `query_set`.
pub fn evaluate_query_set<'a, F: Field>(
    polys: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
    query_set: &QuerySet<'a, F>,
) -> Evaluations<'a, F> {
    let polys = BTreeMap::from_iter(polys.into_iter().map(|p| (p.label(), p)));
    let mut evaluations = Evaluations::new();
    for (label, (_, point)) in query_set {
        let poly = polys
            .get(label)
            .expect("polynomial in evaluated lc is not found");
        let eval = poly.evaluate(*point);
        evaluations.insert((label.clone(), *point), eval);
    }
    evaluations
}

/// Evaluate the given polynomials at `query_set` and returns a Vec<((poly_label, point_label), eval)>)
pub fn evaluate_query_set_to_vec<'a, F: Field>(
    polys: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
    query_set: &QuerySet<'a, F>,
) -> Vec<((String, String), F)> {
    // use std::{
    //     collections::BTreeMap,
    //     iter::FromIterator,
    // };
    let polys = BTreeMap::from_iter(polys.into_iter().map(|p| (p.label(), p)));
    let mut v = Vec::new();
    for (label, (point_label, point)) in query_set {
        let poly = polys
            .get(label)
            .expect("polynomial in evaluated lc is not found");
        let eval = poly.evaluate(*point);
        v.push(((label.clone(), point_label.clone()), eval));
    }
    v
}

/// Generic conversion of an LC query set into a poly query set, by
/// considering every non-trivial poly of an LC to be evaluated at each
/// point the LC is queried.
fn lc_query_set_to_poly_query_set<'a, F: 'a + Field>(
    linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
    query_set: &QuerySet<F>,
) -> QuerySet<'a, F> {
    let mut poly_query_set = QuerySet::new();
    let lc_s = linear_combinations.into_iter().map(|lc| (lc.label(), lc));
    let linear_combinations = BTreeMap::from_iter(lc_s);
    for (lc_label, (point_label, point)) in query_set {
        if let Some(lc) = linear_combinations.get(lc_label) {
            // select the non-trivial polynomials in the LC
            for (_, poly_label) in lc.iter().filter(|(_, l)| !l.is_one()) {
                // add the poly to be queried at the point
                if let LCTerm::PolyLabel(l) = poly_label {
                    poly_query_set.insert((l.into(), (point_label.clone(), *point)));
                }
            }
        }
    }
    poly_query_set
}

#[cfg(test)]
pub mod tests {
    use crate::rng::FiatShamirRngSeed;
    use crate::*;
    use algebra::{serialize::test_canonical_serialize_deserialize, Field, SemanticallyValid};
    use rand::{distributions::Distribution, thread_rng, Rng};

    fn setup_test_fs_rng<F, PC>() -> PC::RandomOracle
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let mut fs_rng_seed_builder = <PC::RandomOracle as FiatShamirRng>::Seed::new();
        fs_rng_seed_builder.add_bytes(b"TEST_SEED").unwrap();
        let fs_rng_seed = fs_rng_seed_builder.finalize();
        PC::RandomOracle::from_seed(fs_rng_seed)
    }

    #[derive(Copy, Clone, PartialEq)]
    pub enum NegativeType {
        Values,
        Commitments,
        CommitterKey,
        VerifierKey,
    }

    #[derive(Copy, Clone, Default)]
    struct TestInfo {
        num_iters: usize,
        /// Max segment size
        max_degree: Option<usize>,
        /// Segment size
        supported_degree: Option<usize>,
        num_polynomials: usize,
        enforce_degree_bounds: bool,
        max_num_queries: usize,
        num_equations: Option<usize>,
        segmented: bool,
        negative_type: Option<NegativeType>,
    }

    pub fn bad_degree_bound_test<F, PC>() -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let rng = &mut thread_rng();
        let max_degree = 100;
        let pp = PC::setup(max_degree)?;

        test_canonical_serialize_deserialize(true, &pp);

        for _ in 0..10 {
            let supported_degree = rand::distributions::Uniform::from(1..=max_degree).sample(rng);
            assert!(
                max_degree >= supported_degree,
                "max_degree < supported_degree"
            );

            let mut labels = Vec::new();
            let mut polynomials = Vec::new();
            let mut degree_bounds = Vec::new();

            for i in 0..10 {
                let label = format!("Test{}", i);
                labels.push(label.clone());
                let poly = Polynomial::rand(supported_degree, rng);

                let degree_bound = 1usize;
                let hiding_bound = Some(1);
                degree_bounds.push(degree_bound);

                polynomials.push(LabeledPolynomial::new(
                    label,
                    poly,
                    Some(degree_bound),
                    hiding_bound,
                ))
            }

            let supported_hiding_bound = polynomials
                .iter()
                .map(|p| p.hiding_bound().unwrap_or(0))
                .max()
                .unwrap_or(0);
            println!("supported degree: {:?}", supported_degree);
            println!("supported hiding bound: {:?}", supported_hiding_bound);
            let (ck, vk) = PC::trim(&pp, supported_degree)?;
            assert!(ck.is_valid());
            assert!(vk.is_valid());
            println!("Trimmed");

            test_canonical_serialize_deserialize(true, &ck);
            test_canonical_serialize_deserialize(true, &vk);

            let (comms, rands) = PC::commit(&ck, &polynomials, Some(rng))?;
            assert!(comms.is_valid());

            let mut query_set = QuerySet::new();
            let mut values = Evaluations::new();
            let point = F::rand(rng);
            for (i, label) in labels.iter().enumerate() {
                query_set.insert((label.clone(), (format!("{}", i), point)));
                let value = polynomials[i].evaluate(point);
                values.insert((label.clone(), point), value);
            }
            println!("Generated query set");

            let mut fs_rng = setup_test_fs_rng::<F, PC>();
            let proof = PC::batch_open(
                &ck,
                &polynomials,
                &comms,
                &query_set,
                &mut fs_rng,
                &rands,
                Some(rng),
            )?;
            assert!(proof.is_valid());

            test_canonical_serialize_deserialize(true, &proof);

            let mut fs_rng = setup_test_fs_rng::<F, PC>();
            let result = PC::batch_check(&vk, &comms, &query_set, &values, &proof, &mut fs_rng)?;
            assert!(result, "proof was incorrect, Query set: {:#?}", query_set);
        }
        Ok(())
    }

    fn test_template<F, PC>(info: TestInfo) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        for _ in 0..info.num_iters {
            let TestInfo {
                max_degree,
                supported_degree,
                num_polynomials,
                enforce_degree_bounds,
                max_num_queries,
                segmented,
                negative_type,
                ..
            } = info;

            let rng = &mut thread_rng();
            // sample random max_degree from 2 up to 64.
            let max_degree =
                max_degree.unwrap_or(rand::distributions::Uniform::from(2..=64).sample(rng));
            let pp = PC::setup(max_degree)?;

            test_canonical_serialize_deserialize(true, &pp);

            // sample supported_degree if not defined
            let supported_degree = match supported_degree {
                Some(0) => 0,
                Some(d) => d,
                None => rand::distributions::Uniform::from(1..=max_degree).sample(rng),
            };
            assert!(
                max_degree >= supported_degree,
                "max_degree < supported_degree"
            );
            let mut polynomials = Vec::new();
            let mut degree_bounds = if enforce_degree_bounds {
                Some(Vec::new())
            } else {
                None
            };

            // sample the maximum number of segments from 5 up to 15.
            let seg_mul = rand::distributions::Uniform::from(5..=15).sample(rng);
            let mut labels = Vec::new();
            println!("Sampled supported degree");

            // sample `max_num_queries` query points
            let num_points_in_query_set =
                rand::distributions::Uniform::from(1..=max_num_queries).sample(rng);
            for i in 0..num_polynomials {
                let label = format!("Test{}", i);
                labels.push(label.clone());

                // sample polynomial of random degree
                let degree;
                if segmented {
                    // sample degree from 5*`supported_degree` up to `seg_mul`*`supported_degree`
                    degree = if supported_degree > 0 {
                        rand::distributions::Uniform::from(1..=supported_degree).sample(rng)
                    } else {
                        0
                    } * seg_mul;
                } else {
                    // sample degree from 1 up to `supported_degree`
                    degree = if supported_degree > 0 {
                        rand::distributions::Uniform::from(1..=supported_degree).sample(rng)
                    } else {
                        0
                    }
                }
                let poly = Polynomial::rand(degree, rng);
                println!("Poly {} degree: {}", i, degree);

                // If specified, we sample any degree bound larger than the degree of the
                // polynomial.
                let degree_bound = if let Some(degree_bounds) = &mut degree_bounds {
                    let segment_size = (supported_degree + 1).next_power_of_two();
                    let num_segments = (degree + 1) / segment_size
                        + if (degree + 1) % segment_size == 0 {
                            0
                        } else {
                            1
                        };
                    let range =
                        rand::distributions::Uniform::from(degree..num_segments * segment_size);
                    let degree_bound = range.sample(rng);
                    degree_bounds.push(degree_bound);
                    Some(degree_bound)
                } else {
                    None
                };

                // Sample hiding bound. The concrete value > 0 does not matter.
                // TODO: Beyond `Some` or `None`, the hiding_bound is not used by the dlog PC,
                // as randomization up to a certain number of queries is outsourced.
                // We should think about how to treat that in future.
                let hiding_bound = if num_points_in_query_set >= degree {
                    Some(degree)
                } else {
                    Some(num_points_in_query_set)
                };
                println!("Hiding bound: {:?}", hiding_bound);

                polynomials.push(LabeledPolynomial::new(
                    label,
                    poly,
                    degree_bound,
                    hiding_bound,
                ))
            }
            let supported_hiding_bound = polynomials
                .iter()
                .map(|p| p.hiding_bound().unwrap_or(0))
                .max()
                .unwrap_or(0);
            println!("supported degree: {:?}", supported_degree);
            println!("supported hiding bound: {:?}", supported_hiding_bound);
            println!("num_points_in_query_set: {:?}", num_points_in_query_set);
            let (mut ck, mut vk) = PC::trim(&pp, supported_degree)?;

            if negative_type.is_some() && negative_type.unwrap() == NegativeType::CommitterKey {
                ck.randomize();
            }

            if negative_type.is_some() && negative_type.unwrap() == NegativeType::VerifierKey {
                vk.randomize();
            }

            assert!(ck.is_valid());
            assert!(vk.is_valid());

            println!("Trimmed");

            test_canonical_serialize_deserialize(true, &ck);
            test_canonical_serialize_deserialize(true, &vk);

            let (mut comms, rands) = PC::commit(&ck, &polynomials, Some(rng))?;
            if negative_type.is_some() && negative_type.unwrap() == NegativeType::Commitments {
                for comm in comms.iter_mut() {
                    comm.randomize();
                }
            }

            assert!(comms.is_valid());

            // Construct "symmetric" query set, over which every polynomial
            // is to be queried
            let mut query_set = QuerySet::new();
            let mut values = Evaluations::new();
            // let mut point = F::one();
            for _ in 0..num_points_in_query_set {
                let point = F::rand(rng);
                for (i, label) in labels.iter().enumerate() {
                    query_set.insert((label.clone(), (format!("{}", i), point)));
                    let value = polynomials[i].evaluate(point);
                    if negative_type.is_some() && negative_type.unwrap() == NegativeType::Values {
                        values.insert((label.clone(), point), F::rand(rng));
                    } else {
                        values.insert((label.clone(), point), value);
                    }
                }
            }
            println!("Generated query set");

            let mut fs_rng = setup_test_fs_rng::<F, PC>();
            let proof = PC::batch_open(
                &ck,
                &polynomials,
                &comms,
                &query_set,
                &mut fs_rng,
                &rands,
                Some(rng),
            )?;

            assert!(proof.is_valid());

            test_canonical_serialize_deserialize(true, &proof);

            // Assert success using the same key
            let mut fs_rng = setup_test_fs_rng::<F, PC>();
            let result = PC::batch_check(&vk, &comms, &query_set, &values, &proof, &mut fs_rng)?;
            if !result {
                println!(
                    "Failed with {} polynomials, num_points_in_query_set: {:?}",
                    num_polynomials, num_points_in_query_set
                );
                println!("Degree of polynomials:",);
                for poly in polynomials {
                    println!("Degree: {:?}", poly.degree());
                }
                return Err(Error::IncorrectProof.into());
            }

            // Assert success using a bigger key
            let bigger_degree = max_degree * 2;
            let pp = PC::setup(bigger_degree)?;
            let (_, vk) = PC::trim(&pp, bigger_degree)?;

            let mut fs_rng = setup_test_fs_rng::<F, PC>();
            assert!(PC::batch_check(
                &vk,
                &comms,
                &query_set,
                &values,
                &proof,
                &mut fs_rng
            )?);
        }
        Ok(())
    }

    fn equation_test_template<F, PC>(info: TestInfo) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let TestInfo {
            num_iters,
            max_degree,
            supported_degree,
            num_polynomials,
            enforce_degree_bounds,
            max_num_queries,
            num_equations,
            ..
        } = info;

        let rng = &mut thread_rng();
        let max_degree =
            max_degree.unwrap_or(rand::distributions::Uniform::from(2..=64).sample(rng));
        let pp = PC::setup(max_degree)?;

        for _ in 0..num_iters {
            let supported_degree = supported_degree
                .unwrap_or(rand::distributions::Uniform::from(1..=max_degree).sample(rng));
            assert!(
                max_degree >= supported_degree,
                "max_degree < supported_degree"
            );
            let mut polynomials = Vec::new();
            let mut degree_bounds = if enforce_degree_bounds {
                Some(Vec::new())
            } else {
                None
            };

            let mut labels = Vec::new();
            println!("Sampled supported degree");

            // Generate polynomials
            let num_points_in_query_set =
                rand::distributions::Uniform::from(1..=max_num_queries).sample(rng);
            for i in 0..num_polynomials {
                let label = format!("Test{}", i);
                labels.push(label.clone());
                let degree = rand::distributions::Uniform::from(1..=supported_degree).sample(rng);
                let poly = Polynomial::rand(degree, rng);

                let degree_bound = if let Some(degree_bounds) = &mut degree_bounds {
                    if rng.gen() {
                        let range = rand::distributions::Uniform::from(degree..=supported_degree);
                        let degree_bound = range.sample(rng);
                        degree_bounds.push(degree_bound);
                        Some(degree_bound)
                    } else {
                        None
                    }
                } else {
                    None
                };

                let hiding_bound = if num_points_in_query_set >= degree {
                    Some(degree)
                } else {
                    Some(num_points_in_query_set)
                };
                println!("Hiding bound: {:?}", hiding_bound);

                polynomials.push(LabeledPolynomial::new(
                    label,
                    poly,
                    degree_bound,
                    hiding_bound,
                ))
            }
            println!("supported degree: {:?}", supported_degree);
            println!("num_points_in_query_set: {:?}", num_points_in_query_set);
            println!("{:?}", degree_bounds);
            println!("{}", num_polynomials);
            println!("{}", enforce_degree_bounds);

            let (ck, vk) = PC::trim(&pp, supported_degree)?;

            assert!(ck.is_valid());
            assert!(vk.is_valid());

            println!("Trimmed");

            let (comms, rands) = PC::commit(&ck, &polynomials, Some(rng))?;
            assert!(comms.is_valid());

            // Let's construct our equations
            let mut linear_combinations = Vec::new();
            let mut query_set = QuerySet::new();
            let mut values = Evaluations::new();
            for i in 0..num_points_in_query_set {
                let point = F::rand(rng);
                for j in 0..num_equations.unwrap() {
                    let label = format!("query {} eqn {}", i, j);
                    let mut lc = LinearCombination::empty(label.clone());

                    let mut value = F::zero();
                    let should_have_degree_bounds: bool = rng.gen();
                    for (k, label) in labels.iter().enumerate() {
                        if should_have_degree_bounds {
                            value += &polynomials[k].evaluate(point);
                            lc.push((F::one(), label.to_string().into()));
                            break;
                        } else {
                            let poly = &polynomials[k];
                            if poly.degree_bound().is_some() {
                                continue;
                            } else {
                                assert!(poly.degree_bound().is_none());
                                let coeff = F::rand(rng);
                                value += &(coeff * poly.evaluate(point));
                                lc.push((coeff, label.to_string().into()));
                            }
                        }
                    }
                    values.insert((label.clone(), point), value);
                    if !lc.is_empty() {
                        linear_combinations.push(lc);
                        // Insert query
                        query_set.insert((label.clone(), (format!("{}", i), point)));
                    }
                }
            }
            if linear_combinations.is_empty() {
                continue;
            }
            println!("Generated query set");
            println!("Linear combinations: {:?}", linear_combinations);

            let mut fs_rng = setup_test_fs_rng::<F, PC>();
            let proof = PC::open_combinations(
                &ck,
                &linear_combinations,
                &polynomials,
                &comms,
                &query_set,
                &mut fs_rng,
                &rands,
                Some(rng),
            )?;
            assert!(proof.is_valid());

            println!("Generated proof");

            let mut fs_rng = setup_test_fs_rng::<F, PC>();
            let result = PC::check_combinations(
                &vk,
                &linear_combinations,
                &comms,
                &query_set,
                &values,
                &proof,
                &mut fs_rng,
            )?;

            if !result {
                println!(
                    "Failed with {} polynomials, num_points_in_query_set: {:?}",
                    num_polynomials, num_points_in_query_set
                );
                println!("Degree of polynomials:",);
                for poly in polynomials {
                    println!("Degree: {:?}", poly.degree());
                }
            }
            assert!(
                result,
                "proof was incorrect, equations: {:#?}",
                linear_combinations
            );
        }
        Ok(())
    }

    pub fn constant_poly_test<F, PC>(negative_type: Option<NegativeType>) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 1,
            enforce_degree_bounds: false,
            max_num_queries: 1,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn single_poly_test<F, PC>(negative_type: Option<NegativeType>) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 1,
            enforce_degree_bounds: false,
            max_num_queries: 1,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn linear_poly_degree_bound_test<F, PC>(
        negative_type: Option<NegativeType>,
    ) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: Some(2),
            supported_degree: Some(1),
            num_polynomials: 1,
            enforce_degree_bounds: true,
            max_num_queries: 1,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn single_poly_degree_bound_test<F, PC>(
        negative_type: Option<NegativeType>,
    ) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 1,
            enforce_degree_bounds: true,
            max_num_queries: 1,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn quadratic_poly_degree_bound_multiple_queries_test<F, PC>(
        negative_type: Option<NegativeType>,
    ) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: Some(3),
            supported_degree: Some(2),
            num_polynomials: 1,
            enforce_degree_bounds: true,
            max_num_queries: 2,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn two_poly_four_points_test<F, PC>(
        negative_type: Option<NegativeType>,
    ) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 1,
            max_degree: Some(1024),
            supported_degree: Some(1024),
            num_polynomials: 2,
            enforce_degree_bounds: true,
            max_num_queries: 4,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn single_poly_degree_bound_multiple_queries_test<F, PC>(
        negative_type: Option<NegativeType>,
    ) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 1,
            enforce_degree_bounds: true,
            max_num_queries: 2,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn two_polys_degree_bound_single_query_test<F, PC>(
        negative_type: Option<NegativeType>,
    ) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 2,
            enforce_degree_bounds: true,
            max_num_queries: 1,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn full_end_to_end_test<F, PC>(negative_type: Option<NegativeType>) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 10,
            enforce_degree_bounds: true,
            max_num_queries: 5,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn segmented_test<F, PC>(negative_type: Option<NegativeType>) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 10,
            enforce_degree_bounds: true,
            max_num_queries: 5,
            segmented: true,
            negative_type,
            ..Default::default()
        };
        test_template::<F, PC>(info)
    }

    pub fn full_end_to_end_equation_test<F, PC>(
        negative_type: Option<NegativeType>,
    ) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 10,
            enforce_degree_bounds: true,
            max_num_queries: 5,
            num_equations: Some(10),
            segmented: false,
            negative_type,
            ..Default::default()
        };
        equation_test_template::<F, PC>(info)
    }

    pub fn single_equation_test<F, PC>(negative_type: Option<NegativeType>) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 1,
            enforce_degree_bounds: false,
            max_num_queries: 1,
            num_equations: Some(1),
            segmented: false,
            negative_type,
            ..Default::default()
        };
        equation_test_template::<F, PC>(info)
    }

    pub fn two_equation_test<F, PC>(negative_type: Option<NegativeType>) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 2,
            enforce_degree_bounds: false,
            max_num_queries: 1,
            num_equations: Some(2),
            segmented: false,
            negative_type,
            ..Default::default()
        };
        equation_test_template::<F, PC>(info)
    }

    pub fn two_equation_degree_bound_test<F, PC>(
        negative_type: Option<NegativeType>,
    ) -> Result<(), PC::Error>
    where
        F: Field,
        PC: PolynomialCommitment<F>,
    {
        let info = TestInfo {
            num_iters: 100,
            max_degree: None,
            supported_degree: None,
            num_polynomials: 2,
            enforce_degree_bounds: true,
            max_num_queries: 1,
            num_equations: Some(2),
            segmented: false,
            negative_type,
            ..Default::default()
        };
        equation_test_template::<F, PC>(info)
    }
}
