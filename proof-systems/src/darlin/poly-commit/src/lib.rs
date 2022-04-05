//! A crate for linear polynomial commitment schemes.
//! Supports verifier splitting into a succinct and non-succinct (or "hard") part,
//! and provides default implementations for more expressive evaluation claims:
//! * "multi-poly single-point", which uses the standard batching technique
//!   based on random linear combination,
//! * "multi-poly multi-point" which is the "batch evaluation" protocol from
//!   Boneh et al. [HaloInfinite]
//! The crate additionally implements generic domain extension of linear polynomial
//! commitment schemes as described in [Darlin].
//!
//! [HaloInfinite]: https://eprint.iacr.org/2020/1536
//! [Darlin]: https://eprint.iacr.org/2021/930/20210709:180459
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public, variant_size_differences)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_mut)]
#![deny(unused_imports)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]
#![allow(unused_assignments)]
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

#[cfg(test)]
mod tests;

pub use algebra::fft::DensePolynomial as Polynomial;
use algebra::{serialize::*, Field, Group, LinearCombination, PrimeField, SemanticallyValid};
use digest::Digest;
use fiat_shamir::FiatShamirRng;
use num_traits::{One, Zero};
use rand_core::RngCore;
use std::collections::HashMap;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
    iter::FromIterator,
    rc::Rc,
    string::{String, ToString},
    vec::Vec,
};
#[cfg(feature = "circuit-friendly")]
use algebra::ToBits;

/// Data structures for linear polynomial commitment schemes.
pub mod data_structures;
pub use data_structures::*;

/// Errors pertaining to query maps.
pub mod error;
pub use error::*;

/// A random number generator that bypasses some limitations of the Rust borrow
/// checker.
pub mod optional_rng;

/// Domain extension of [`PolynomialCommitment`].
pub mod domain_extended;
pub use domain_extended::*;

/// The [BCMS20](https://eprint.iacr.org/2020/499) variant of the dlog commitment scheme.
pub mod ipa_pc;

/// Gadget to verify opening proofs of a linear polynomial commitment scheme
#[cfg(feature = "circuit-friendly")]
pub mod constraints;
#[cfg(feature = "circuit-friendly")]
pub use constraints::*;

#[cfg(feature = "boneh-with-single-point-batch")]
const H_POLY_LABEL: &str = "h-poly";

/// `QueryMap` is the set of queries that are to be made to a set of labeled polynomials or linear combinations.
///
///  Each element of a `QueryMap` maps a `point_label` to a pair (`point`, `poly_labels`), where
///  * `point_label` is the label for the point (e.g., "beta"),
///  * `point` is the field element that `p[label]` is to be queried at and
///  * `poly_labels` is the list of polys that must be queried at `point`,
pub type QueryMap<'a, F> = BTreeMap<PointLabel, (F, BTreeSet<PolynomialLabel>)>;

/// `Evaluations` is the result of querying a set of labeled polynomials or linear combinations
/// `p` at a `QueryMap` `Q`.
/// It maps each element of `Q` to the resulting evaluation, e.g. `evaluation.get((label, query))`
/// should equal to `p[label].evaluate(query)`.
pub type Evaluations<'a, F> = BTreeMap<(PolynomialLabel, PointLabel), F>;

// convert a sequence of field elements to a sequence of bits, concatenating their big-endian bit representations
#[cfg(feature = "boneh-with-single-point-batch")]
fn field_elements_to_bits<'a, F: Field>(
    fes: impl Iterator<Item=&'a F>,
) -> Vec<bool> {
    fes.flat_map(|val| val.write_bits()).collect::<Vec<_>>()
}

/// Default implementation of `single_point_multi_poly_open` for `PolynomialCommitment`,
/// employed as a building block also by domain extended polynomial commitments
pub(crate) fn single_point_multi_poly_open<'a,
    G: Group,
    PC: PolynomialCommitment<G>,
    IP: IntoIterator<Item = &'a LabeledPolynomial<G::ScalarField>>,
    IR: IntoIterator<Item = &'a LabeledRandomness<PC::Randomness>>,
>(
        ck: &PC::CommitterKey,
        labeled_polynomials: IP,
        point: G::ScalarField,
        fs_rng: &mut PC::RandomOracle,
        labeled_randomnesses: IR,
        // The optional rng for additional internal randomness of open()
        rng: Option<&mut dyn RngCore>,
    ) -> Result<PC::Proof, PC::Error> {
        // as the statement/assertion of the opening proof is already bound to the interal state
        // of the fr_rng, we simply sample the challenge scalar for the random linear combination
        let lambda = PC::challenge_to_scalar(fs_rng.get_challenge::<128>()?.to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;
        let mut is_hiding = false;

        // compute the random linear combinations using the powers of lambda

        let poly_lc = LinearCombination::new_from_val(
            &lambda,
            labeled_polynomials
                .into_iter()
                .map(|poly| {
                    if poly.is_hiding() {
                        is_hiding = true;
                    }
                    poly.polynomial()
                })
                .collect(),
        );

        let rands_lc = if is_hiding {
            LinearCombination::new_from_val(
                &lambda,
                labeled_randomnesses
                    .into_iter()
                    .map(|rand| rand.randomness())
                    .collect(),
            )
        } else {
            LinearCombination::empty()
        };

        PC::open_lc(ck, poly_lc, point, is_hiding, rands_lc, fs_rng, rng)
    }

/// Default implementation of `succinct_verify_single_point_multi_poly` for `PolynomialCommitment`,
/// employed as a building block also by domain extended polynomial commitments
pub(crate) fn single_point_multi_poly_succinct_verify<'a,
    G: Group,
    PC: PolynomialCommitment<G>,
    IC: IntoIterator<Item = &'a LabeledCommitment<PC::Commitment>>,
    IV: IntoIterator<Item = &'a G::ScalarField>,
>(
    vk: &PC::VerifierKey,
    labeled_commitments: IC,
    point: G::ScalarField,
    values: IV,
    proof: &PC::Proof,
    // This implementation assumes that the commitments, point and evaluations are
    // already bound to the internal state of the Fiat Shamir rng
    fs_rng: &mut PC::RandomOracle,
) -> Result<Option<PC::VerifierState>, PC::Error> {
    let combine_time = start_timer!(|| "Single point multi poly verify combine time");

    let lambda = PC::challenge_to_scalar(fs_rng.get_challenge::<128>()?.to_vec())
        .map_err(|e| Error::Other(e.to_string()))?;

    let commitments_lc = LinearCombination::new_from_val(
        &lambda,
        labeled_commitments
            .into_iter()
            .map(|comm| comm.commitment())
            .collect(),
    );

    let combined_value =
        LinearCombination::new_from_val(&lambda, values.into_iter().collect()).combine();

    end_timer!(combine_time);

    PC::succinct_verify_lc(vk, commitments_lc, point, combined_value, proof, fs_rng)
}

/// Default implementation of `multi_point_multi_poly_open` for `PolynomialCommitment`,
/// employed as a building block also by domain extended polynomials commitments
fn multi_point_multi_poly_open<'a, 'b,
    G: Group,
    PC: PolynomialCommitment<G>,
    LabelIT: 'b + IntoIterator<Item=PolynomialLabel> + Clone,
    //PolyIT: IntoIterator<Item = &'a LabeledPolynomial<G::ScalarField>>,
    QueryIT: IntoIterator<Item = (&'b PointLabel, &'b (G::ScalarField, LabelIT))>,
    RandIT: IntoIterator<Item = &'a LabeledRandomness<PC::Randomness>>,
>(
    ck: &PC::CommitterKey,
    poly_map: PolyMap<&'a PolynomialLabel, &'a LabeledPolynomial<G::ScalarField>>,
    query_map: QueryIT, //&QueryMap<G::ScalarField>,
    fs_rng: &mut PC::RandomOracle,
    labeled_randomnesses: RandIT,
    // The optional rng for additional internal randomness of open()
    mut rng: Option<&mut dyn RngCore>,
) -> Result<PC::MultiPointProof, PC::Error>
where
    <QueryIT as IntoIterator>::IntoIter: Clone
{
    // The multi-point multi-poly assertion is rephrased as polynomial identity over the query map
    // Q = {x_1,...,x_m},
    //
    //      Sum_i  lambda^i z_i(X) * (p_i(X) - y_i)  = h(X) * z(X),
    //
    // where `z_i(X) = Prod_{x_j!=x_i} (x - x_j)` and `z(X)` is the vanishing polynomial of the
    // query map. The identity is proven by providing h(X) and showing that for a random x outside
    // the query map, the "mult-point multi-poly opening combination"
    //
    //       LC_x(p_i(X),h(X)) = Sum_i  lambda^i z_i(x)/z(x) * p_i(X)  - h(X)
    //
    // opens to the expected value `v = Sum_i lambda^i z_i(x)/z(x)* y_i`.
    let batch_time = start_timer!(|| "Multi poly multi point batching.");

    let combine_time = start_timer!(|| "Combining polynomials, randomness, and commitments.");


    let rands_map: PolyMap<_, _> = labeled_randomnesses
        .into_iter()
        .map(|rand| (rand.label(), rand))
        .collect();

    // as the statement of the opening proof is already bound to the interal state of the fs_rng,
    // we simply sample the challenge scalar for the random linear combination
    let lambda = PC::challenge_to_scalar(fs_rng.get_challenge::<128>()?.to_vec())
        .map_err(|e| Error::Other(e.to_string()))?;

    let mut has_hiding = false;

    let h_poly_time = start_timer!(|| "Compute h(X) polynomial");

    // h(X)
    let mut h_polynomial = Polynomial::zero();

    // Save evaluation points for later
    let mut eval_points = std::collections::HashSet::new();

    let query_map_iter = query_map.into_iter();

    #[cfg(not(feature = "boneh-with-single-point-batch"))]
        let query_map_iter_cloned = query_map_iter.clone();

    for (_point_label, (point, poly_labels)) in query_map_iter {
        eval_points.insert(*point);

        let mut cur_challenge = G::ScalarField::one();

        // (X - x_i)
        let x_polynomial =
            Polynomial::from_coefficients_slice(&[-(*point), G::ScalarField::one()]);
        let mut cur_h_polynomial = Polynomial::zero();

        for label in poly_labels.clone() {
            let labeled_polynomial = *poly_map.get(&label).ok_or(Error::MissingPolynomial {
                label: label.to_string(),
            })?;

            if labeled_polynomial.is_hiding() {
                has_hiding = true;
            }

            // y_i
            let y_i = labeled_polynomial.polynomial().evaluate(*point);

            // (p_i(X) - y_i) / (X - x_i)
            let polynomial = labeled_polynomial.polynomial()
                - &Polynomial::from_coefficients_slice(&[y_i]);

            // h(X) = SUM( lambda^i * ((p_i(X) - y_i) / (X - x_i)) )
            cur_h_polynomial += (cur_challenge, &polynomial);

            // lambda^i
            cur_challenge = cur_challenge * &lambda;
        }

        h_polynomial += &cur_h_polynomial/&x_polynomial;
    }

    end_timer!(h_poly_time);

    let commit_time = start_timer!(|| format!(
            "Commit to h(X) polynomial of degree {}",
            h_polynomial.degree()
        ));

    let (h_commitment, h_randomness) = PC::commit(
        ck,
        &h_polynomial,
        has_hiding,
        if has_hiding {
            if rng.is_none() {
                end_timer!(commit_time);
                Err(Error::Other("Rng not set".to_owned()))?
            }
            Some(rng.as_mut().unwrap())
        } else {
            None
        },
    )?;

    end_timer!(commit_time);

    let open_time = start_timer!(|| "Open LC(p_1(X),p_2(X),...,p_m(X),h(X)) polynomial");

    // Fresh random challenge x for multi-point to single-point reduction.
    // Except the `batch_commitment`, all other commitments are already bound
    // to the internal state of the Fiat-Shamir
    fs_rng
        .record(h_commitment.clone())
        .map_err(Error::FiatShamirTransformError)?;

    // in this case there is no need to rely on Self::challenge_to_scalar, as the conversion
    // is not implementation specific
    let x_point = read_fe_from_challenge::<G::ScalarField>(
        fs_rng.get_challenge::<128>()?.to_vec())
        .map_err(|e| Error::Other(e.to_string()))?;

    // Assert x_point != x_1, ..., x_m
    // This is needed as we use a slightly optimized LC, which costs one
    // scalar multiplication.
    if eval_points.iter().any(|eval_point| eval_point == &x_point) {
        end_timer!(open_time);
        Err(Error::Other(
            "sampled a challenge equal to one of the evaluation points".to_owned(),
        ))?
    }

    #[cfg(not(feature = "boneh-with-single-point-batch"))]
        return {
        // LC(p_1(X),p_2(X),...,p_m(X),h(X))
        // NOTE: We can use LC here and call open_lc but it's not really worth it
        //       either in terms of efficiency and code complexity
        let mut lc_polynomial = Polynomial::zero();
        let mut lc_randomness = PC::Randomness::zero();


        for (_point_label, (point, poly_labels)) in query_map_iter_cloned {
            let mut cur_challenge = G::ScalarField::one();
            let z_i_over_z_value = (x_point - point).inverse().unwrap();
            for label in poly_labels.clone() {
                let labeled_polynomial = *poly_map.get(&label).ok_or(Error::MissingPolynomial {
                    label: label.to_string(),
                })?;

                let labeled_randomness = *rands_map.get(&label).ok_or(Error::MissingRandomness {
                    label: label.to_string(),
                })?;

                lc_polynomial += (cur_challenge * z_i_over_z_value, labeled_polynomial.polynomial());

                if has_hiding {
                    lc_randomness += &(labeled_randomness.randomness().clone() * &(cur_challenge * z_i_over_z_value));
                }

                // lambda^i
                cur_challenge = cur_challenge * &lambda;
            }
        }

        // LC(p_1(X),p_2(X),...,p_m(X),h(X)) = SUM ( lamda^i * z_i(x)/z(x) * p_i(X) ) -  h(X)
        lc_polynomial -= &h_polynomial;

        if has_hiding {
            lc_randomness -= &h_randomness;
        }

        end_timer!(open_time);
        end_timer!(combine_time);

        let proof = PC::open(
            ck,
            lc_polynomial,
            x_point,
            has_hiding,
            lc_randomness,
            fs_rng,
            rng,
        )?;

        end_timer!(batch_time);

        Ok(PC::MultiPointProof::new(proof, h_commitment.clone()))
    };

    #[cfg(feature="boneh-with-single-point-batch")]
        return {
        let labeled_h_polynomial = LabeledPolynomial::new(H_POLY_LABEL.to_string(), h_polynomial, has_hiding);
        let labeled_h_randomness = LabeledRandomness::new(H_POLY_LABEL.to_string(), h_randomness);

        // evaluate each polynomial in `labeled_polynomials` and the h-polynomial over the batch evaluation point
        let (mut polynomials, evaluations): (Vec<_>, Vec<_>) = poly_map.into_iter()
            .map(|(_, poly)| {
                (poly, poly.evaluate(x_point))
            }).unzip();

        let randomnesses = rands_map.into_iter().map(|(_, rand)| rand).chain(vec![&labeled_h_randomness]);

        polynomials.push(&labeled_h_polynomial);


        // absorb evaluations of polynomials over x_point
        fs_rng.record::<G::BaseField, _>(field_elements_to_bits(evaluations.iter()).as_slice())?;

        end_timer!(open_time);
        end_timer!(combine_time);

        let proof = PC::single_point_multi_poly_open(ck, polynomials, x_point, fs_rng, randomnesses, rng)?;


        end_timer!(batch_time);

        // note that evaluations are put in the proof according to the lexicographical order
        // of the labels of the polynomials they refer to
        Ok(PC::MultiPointProof::new(proof, h_commitment, evaluations))

    };
}

/// Default implementation of `succinct_multi_point_multi_poly_verify` for `PolynomialCommitment`,
/// which is employed as a building block also by domain extended commitments
#[cfg(not(feature = "boneh-with-single-point-batch"))]
fn succinct_multi_point_multi_poly_verify<'a,'b,
    G: Group,
    PC: PolynomialCommitment<G>,
    LabelIT: 'b + IntoIterator<Item=PolynomialLabel> + Clone,
    QueryIT: IntoIterator<Item = (&'b PointLabel, &'b (G::ScalarField, LabelIT))>,
>(
    vk: &PC::VerifierKey,
    commitment_map: PolyMap<&'a PolynomialLabel, &'a LabeledCommitment<PC::Commitment>>,
    query_map: QueryIT,
    evaluations: &Evaluations<G::ScalarField>,
    multi_point_proof: &PC::MultiPointProof,
    // This implementation assumes that the commitments, query map and evaluations are already recorded by the Fiat Shamir rng
    fs_rng: &mut PC::RandomOracle,
) -> Result<Option<PC::VerifierState>, PC::Error> {
    let combine_time = start_timer!(|| "Multi point multi poly verify combine time");


    // lambda
    let lambda = PC::challenge_to_scalar(fs_rng.get_challenge::<128>()?.to_vec())
        .map_err(|e| Error::Other(e.to_string()))?;

    // Fresh random challenge x
    fs_rng
        .record(multi_point_proof.get_h_commitment().clone())
        .map_err(Error::FiatShamirTransformError)?;

    // in this case there is no need to rely on Self::challenge_to_scalar, as the conversion
    // is not implementation specific
    let x_point = read_fe_from_challenge::<G::ScalarField>(
        fs_rng.get_challenge::<128>()?.to_vec())
        .map_err(|e| Error::Other(e.to_string()))?;
    // LC(C): reconstructed commitment to LC(p_1(X),p_2(X),...,p_m(X),h(X))
    let mut lc_commitment = PC::Commitment::zero();

    // Expected value wich LC(p_1(X),p_2(X),...,p_m(X),h(X)) opens to
    let mut lc_value = G::ScalarField::zero();

    for (point_label, (point, poly_labels)) in query_map {
        // Assert x_point != x_1, ..., x_m
        if point == &x_point {
            Err(Error::Other(
                "sampled a challenge equal to one of the evaluation points".to_owned(),
            ))?
        }

        // (X - x_i)
        let x_polynomial =
            Polynomial::from_coefficients_slice(&[-(*point), G::ScalarField::one()]);

        // z_i(x)/z(x) = 1 / (x - x_i).
        // unwrap cannot fail as x-x_i is guaranteed to be non-zero.
        let z_i_over_z_value = x_polynomial.evaluate(x_point).inverse().unwrap();

        let mut cur_challenge = G::ScalarField::one();

        for label in poly_labels.clone() {
            let labeled_commitment =
                *commitment_map.get(&label).ok_or(Error::MissingCommitment {
                    label: label.to_string(),
                })?;

            // y_i
            let y_i = *evaluations
                .get(&(label.clone(), point_label.clone()))
                .ok_or(Error::MissingEvaluation {
                    label: label.to_string(),
                })?;

            lc_commitment += &(labeled_commitment.commitment().clone()
                * &(z_i_over_z_value * cur_challenge));

            lc_value += y_i * cur_challenge * z_i_over_z_value;

            // lambda^i
            cur_challenge = cur_challenge * &lambda;
        }
    }

    lc_commitment += &(-multi_point_proof.get_h_commitment().clone());

    end_timer!(combine_time);

    PC::succinct_verify(
        vk,
        &lc_commitment,
        x_point,
        lc_value,
        multi_point_proof.get_proof(),
        fs_rng,
    )
}

// this type alias defined the data structure employed to map a label to a polynomial/randomness.
// In the boneh-with-single-point-batch version, we employ a BTreeMap as we need to iterate with a deterministic
// order over this map; conversely, in the non boneh-with-single-point-batch version we just need to get elements
// from the map, thus we employ an HashMap for efficiency
#[cfg(feature = "boneh-with-single-point-batch")]
type PolyMap<K, V> = BTreeMap<K, V>;
#[cfg(not(feature = "boneh-with-single-point-batch"))]
type PolyMap<K, V> = HashMap<K, V>;

/// Describes the interface for a homomorphic polynomial commitment scheme with values
/// in a commitment group built on `G`, which means that the commitment is either `G` itself
/// or a direct sum of it.  
///
/// The simple single-polynomial evaluation proof depends on the concrete scheme, whereas
/// more expressive opening proofs are reduced to a simple one by leveraging the homomorphic
/// properties.
/// The interface comes with the additional feature of splitting the verifier into a
/// `succinct` part and `non-succinct` part.
pub trait PolynomialCommitment<G: Group>: Sized {
    /// The committer key for the scheme; used to commit to a polynomial and then
    /// open the commitment to produce an evaluation proof.
    type CommitterKey: PCKey;
    /// The verifier key for the scheme; used to check an evaluation proof.
    type VerifierKey: PCKey;
    /// The verifier state; generated by succinct verify.
    type VerifierState: PCVerifierState;
    /// The commitment to a polynomial.
    type Commitment: Group<BaseField = G::BaseField, ScalarField = G::ScalarField>;
    /// The commitment randomness.
    type Randomness: Group<ScalarField = G::ScalarField>;
    /// A `simple' evaluation proof for single-point (single- or multi-poly) assertions.
    type Proof: PCProof;
    /// A batch evaluation proof in the sense of Boneh (et al.) contains an additional commitment.
    type MultiPointProof: BDFGMultiPointProof<G, Proof = Self::Proof, Commitment = Self::Commitment>;
    /// The error type for the scheme.
    type Error: std::error::Error + From<Error> + From<fiat_shamir::error::Error>;
    /// The stateful Fiat-Shamir random number generator.
    type RandomOracle: FiatShamirRng;

    /// Constructs public parameters when given as input the maximum degree `degree`
    /// for the polynomial commitment scheme.
    fn setup<D: Digest>(
        max_degree: usize,
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), Self::Error>;

    /// Constructs public parameters when given as input the maximum degree `degree`
    /// for the polynomial commitment scheme from given seed
    fn setup_from_seed<D: Digest>(
        max_degree: usize,
        seed: &[u8],
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), Self::Error>;

    /// Computes the commitment of a single polynomial
    fn commit(
        ck: &Self::CommitterKey,
        polynomial: &Polynomial<G::ScalarField>,
        // Set `is_hiding = true` for hiding commitments
        is_hiding: bool,
        // rng for hiding randomness
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Self::Commitment, Self::Randomness), Self::Error>;

    /// The vectorial variant of `fn commit()`. Outputs a vector of commitments
    /// to a set of `polynomials`.
    // If `polynomials[i].is_hiding()`, then the `i`-th commitment is hiding.
    // Hence `rng` should not be `None` if `polynomials[i].is_hiding() == true`
    // for some of the `i`s.
    // If for some `i`, `polynomials[i].is_hiding() == false`, then the
    // corresponding randomness is `G::ScalarField::empty()`.
    fn commit_many<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<G::ScalarField>>,
        // The optional rng for additional internal randomness of open()
        mut rng: Option<&mut dyn RngCore>,
    ) -> Result<
        (
            Vec<LabeledCommitment<Self::Commitment>>,
            Vec<LabeledRandomness<Self::Randomness>>,
        ),
        Self::Error,
    > {
        let mut labeled_commitments = Vec::new();
        let mut labeled_randomnesses = Vec::new();

        let commit_time = start_timer!(|| "Committing to polynomials");
        for labeled_polynomial in labeled_polynomials {
            let polynomial = labeled_polynomial.polynomial();
            let label = labeled_polynomial.label();
            let is_hiding = labeled_polynomial.is_hiding();

            let single_commit_time = start_timer!(|| format!(
                "Polynomial {} of degree {}, and hiding bound {:?}",
                label,
                polynomial.degree(),
                is_hiding,
            ));

            let (commitment, randomness) = Self::commit(
                ck,
                polynomial,
                is_hiding,
                if rng.is_some() {
                    Some(rng.as_mut().unwrap())
                } else {
                    None
                },
            )?;

            let labeled_commitment = LabeledCommitment::new(label.to_string(), commitment);
            let labeled_randomness = LabeledRandomness::new(label.to_string(), randomness);

            labeled_commitments.push(labeled_commitment);
            labeled_randomnesses.push(labeled_randomness);

            end_timer!(single_commit_time);
        }

        end_timer!(commit_time);
        Ok((labeled_commitments, labeled_randomnesses))
    }

    /// Single-point single-poly open, for proving an evaluation claim `p(x) = y`
    /// at a query point `x`.
    /// Note: It is assumed that the state of the Fiat-Shamir random number generator `fs_rng`
    /// is already bound to the evaluation claim, i.e. the commitment of `polynomial`,
    /// the point `x`, and the value `y`.
    fn open(
        ck: &Self::CommitterKey,
        polynomial: Polynomial<G::ScalarField>,
        point: G::ScalarField,
        // Set `is_hiding = true` for zk of the evaluation proof.
        // TODO: let us rename it to `zk`
        is_hiding: bool,
        hiding_randomness: Self::Randomness,
        fs_rng: &mut Self::RandomOracle,
        // The optional rng for additional internal randomness of open()
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error>;

    /// The succinct part of `verify()`.
    fn succinct_verify(
        vk: &Self::VerifierKey,
        commitment: &Self::Commitment,
        point: G::ScalarField,
        value: G::ScalarField,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<Option<Self::VerifierState>, Self::Error>;

    /// The hard part of `verify()`.
    fn hard_verify(vk: &Self::VerifierKey, vs: &Self::VerifierState) -> Result<bool, Self::Error>;

    /// Single-point single-poly verify. Verifies a proof produced by `fn open()`.
    /// The verification function of an opening proof produced by `fn open()`
    fn verify(
        vk: &Self::VerifierKey,
        commitment: &Self::Commitment,
        point: G::ScalarField,
        value: G::ScalarField,
        proof: &Self::Proof,
        // This implementation assumes that the commitments, point and evaluations are already recorded by the Fiat Shamir rng
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error> {
        let check_time = start_timer!(|| "Checking evaluations");

        let verifier_state = Self::succinct_verify(vk, commitment, point, value, proof, fs_rng)?;

        if verifier_state.is_none() {
            end_timer!(check_time);
            Err(Error::FailedSuccinctCheck)?
        }

        let res = Self::hard_verify(vk, &verifier_state.unwrap());

        end_timer!(check_time);

        res
    }

    /// Open a linear combination at a single query point.
    /// Note: this default implementation demands that the state of the Fiat-Shamir
    /// rng is already bound to the evaluation claim (i.e. the linear combination,
    /// the query point and the value).
    fn open_lc(
        ck: &Self::CommitterKey,
        polynomials_lc: LinearCombination<G::ScalarField, Polynomial<G::ScalarField>>,
        point: G::ScalarField,
        is_hiding: bool,
        randomnesses_lc: LinearCombination<G::ScalarField, Self::Randomness>,
        fs_rng: &mut Self::RandomOracle,
        // The optional rng for additional internal randomness of open()
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error> {
        debug_assert!(if is_hiding {
            polynomials_lc.length() == randomnesses_lc.length()
        } else {
            true
        });
        let lc_poly_time = start_timer!(|| "Combine polynomials LC");
        let polynomial = polynomials_lc.combine();
        end_timer!(lc_poly_time);

        let lc_rand_time = start_timer!(|| "Combine randomness LC");
        let randomness = randomnesses_lc.combine();
        end_timer!(lc_rand_time);

        Self::open(ck, polynomial, point, is_hiding, randomness, fs_rng, rng)
    }

    /// The succinct part of `verify_lc()`.
    fn succinct_verify_lc(
        vk: &Self::VerifierKey,
        commitments_lc: LinearCombination<G::ScalarField, Self::Commitment>,
        point: G::ScalarField,
        value: G::ScalarField,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<Option<Self::VerifierState>, Self::Error> {
        let lc_comm_time = start_timer!(|| "Combine commitments LC");
        let commitment = commitments_lc.combine();
        end_timer!(lc_comm_time);

        Self::succinct_verify(vk, &commitment, point, value, proof, fs_rng)
    }

    /// Verify proofs produced by `fn open_lc()`.
    fn verify_lc(
        vk: &Self::VerifierKey,
        commitments_lc: LinearCombination<G::ScalarField, Self::Commitment>,
        point: G::ScalarField,
        value: G::ScalarField,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error> {
        let check_time = start_timer!(|| "Checking evaluations");

        let verifier_state =
            Self::succinct_verify_lc(vk, commitments_lc, point, value, proof, fs_rng)?;

        if verifier_state.is_none() {
            end_timer!(check_time);
            Err(Error::FailedSuccinctCheck)?
        }

        let res = Self::hard_verify(vk, &verifier_state.unwrap());

        end_timer!(check_time);

        res
    }

    /// Transform a challenge to its representation in the scalar field.
    /// 'chal' bits are supposed to be in LE bit order.
    fn challenge_to_scalar(chal: Vec<bool>) -> Result<G::ScalarField, Self::Error> {
        let chal = read_fe_from_challenge::<G::ScalarField>(chal)
            .map_err(|e| Error::Other(e.to_string()))?;
        Ok(chal)
    }

    /// Single-point multi-poly open, for proving an evaluation claim
    ///     `p_i(x) = y_i`, `i=1,...,m`,
    /// sharing the same query point `x`. Reduces the batch of evaluation claims to
    /// that of a random linear combination.
    /// Note: this default implementation demands that the state of the Fiat-Shamir
    /// rng is already bound to the evaluation claim (i.e.  the commitments `label_commitments`,
    /// the point `x`, and the values `v_i`.).
    fn single_point_multi_poly_open<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<G::ScalarField>>,
        point: G::ScalarField,
        fs_rng: &mut Self::RandomOracle,
        labeled_randomnesses: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        // The optional rng for additional internal randomness of open()
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error> {
        single_point_multi_poly_open::<G, Self, _, _>(ck, labeled_polynomials, point, fs_rng, labeled_randomnesses, rng)
    }

    /// The batch evaluation protocol from Boneh et al. [HaloInfinite], for proving a multi-point
    /// multi-poly assertion
    ///  `p_i(x_i) = y_i`, `i=1,...,m`
    /// for a set of `labeled_polynomials`.
    /// Note: this default implementation demands that the state of the Fiat-Shamir
    /// rng is already bound to the evaluation claim (i.e.  the commitments `label_commitments`,
    /// the query map, and the values `v_i`.).
    ///
    /// [HaloInfinite]: https://eprint.iacr.org/2020/1536
    fn multi_point_multi_poly_open<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<G::ScalarField>>,
        query_map: &'a QueryMap<G::ScalarField>,
        fs_rng: &mut Self::RandomOracle,
        labeled_randomnesses: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        // The optional rng for additional internal randomness of open()
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::MultiPointProof, Self::Error> {
        let poly_map: PolyMap<_, _> = labeled_polynomials
            .into_iter()
            .map(|poly| (poly.label(), poly))
            .collect();

        multi_point_multi_poly_open::<G, Self, _, _, _>(ck, poly_map, query_map, fs_rng, labeled_randomnesses, rng)
    }

    /// The succinct part of `single_point_multi_poly_verify()`.
    fn succinct_single_point_multi_poly_verify<'a>(
        vk: &Self::VerifierKey,
        labeled_commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: G::ScalarField,
        values: impl IntoIterator<Item = &'a G::ScalarField>,
        proof: &Self::Proof,
        // This implementation assumes that the commitments, point and evaluations are
        // already bound to the internal state of the Fiat Shamir rng
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<Option<Self::VerifierState>, Self::Error> {
        single_point_multi_poly_succinct_verify::<G, Self, _, _>(vk, labeled_commitments, point, values, proof, fs_rng)
    }

    /// The verifier for proofs generated by `fn single_point_multi_poly_open()`.
    fn single_point_multi_poly_verify<'a>(
        vk: &Self::VerifierKey,
        labeled_commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: G::ScalarField,
        values: impl IntoIterator<Item = &'a G::ScalarField>,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error> {
        let check_time = start_timer!(|| "Checking evaluations");

        let verifier_state = Self::succinct_single_point_multi_poly_verify(
            vk,
            labeled_commitments,
            point,
            values,
            proof,
            fs_rng,
        )?;

        if verifier_state.is_none() {
            end_timer!(check_time);
            Err(Error::FailedSuccinctCheck)?
        }

        let res = Self::hard_verify(vk, &verifier_state.unwrap());

        end_timer!(check_time);

        res
    }

    /// The succinct part of `multi_point_multi_poly_verify()`.
    #[cfg(not(feature = "boneh-with-single-point-batch"))]
    fn succinct_multi_point_multi_poly_verify<'a>(
        vk: &Self::VerifierKey,
        labeled_commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_map: &'a QueryMap<G::ScalarField>,
        evaluations: &Evaluations<G::ScalarField>,
        multi_point_proof: &Self::MultiPointProof,
        // This implementation assumes that the commitments, query map and evaluations are already recorded by the Fiat Shamir rng
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<Option<Self::VerifierState>, Self::Error> {
        let commitment_map: PolyMap<_, _> = labeled_commitments
            .into_iter()
            .map(|commitment| (commitment.label(), commitment))
            .collect();

        succinct_multi_point_multi_poly_verify::<G, Self, _, _>(vk, commitment_map, query_map, evaluations, multi_point_proof, fs_rng)
    }

    #[cfg(feature = "boneh-with-single-point-batch")]
    fn succinct_multi_point_multi_poly_verify<'a>(
        vk: &Self::VerifierKey,
        labeled_commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_map: &QueryMap<G::ScalarField>,
        evaluations: &Evaluations<G::ScalarField>,
        multi_point_proof: &Self::MultiPointProof,
        // This implementation assumes that the commitments, query map and evaluations are already recorded by the Fiat Shamir rng
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<Option<Self::VerifierState>, Self::Error> {
        let combine_time = start_timer!(|| "Multi point multi poly verify combine time");

        // lambda
        let lambda = Self::challenge_to_scalar(fs_rng.get_challenge::<128>()?.to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;

        let h_commitment = LabeledCommitment::new(H_POLY_LABEL.to_string(), multi_point_proof.get_h_commitment().clone());

        // Fresh random challenge x
        fs_rng
            .record(h_commitment.commitment().clone())
            .map_err(Error::FiatShamirTransformError)?;

        // in this case there is no need to rely on Self::challenge_to_scalar, as the conversion
        // is not implementation specific
        let x_point = read_fe_from_challenge::<G::ScalarField>(
            fs_rng.get_challenge::<128>()?.to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;

        let mut lc_value = G::ScalarField::zero();

        // sort commitments according to their labels
        let commitment_map: BTreeMap<PolynomialLabel, _> = labeled_commitments
            .into_iter()
            .map(|commitment| (commitment.label().clone(), commitment))
            .collect();

        // collect commitments sorted to their labels in a vector and construct a map which binds
        // a label of a commitment to its order in the sorted vector
        let (labels_map, mut sorted_commitments): (HashMap<_,_>, Vec<_>) = commitment_map.into_iter().enumerate().map(|(i, (label, comm))|
            ((label, i), comm)
        ).unzip();

        /* fetch evaluations of the input polynomials over x_point from the proof.
        Note that evaluations are sorted in the proof according to the lexicographical order of
        the labels of the polynomials they refers to
        (i.e., values[i] is the evaluation for the polynomial with commitment sorted_commitments[i])
        */
        let values = multi_point_proof.get_evaluations();

        for (point_label, (point, poly_labels)) in query_map {
            let z_i_over_z_value = (x_point - point).inverse().ok_or(Error::Other(format!("batch evaluation point equal to point with label {}", point_label)))?;
            let mut cur_challenge = G::ScalarField::one();
            for label in poly_labels {
                let v_i = values[*labels_map.get(label).ok_or(Error::MissingEvaluation {label: label.clone()})?];

                let y_i = *evaluations.get(&(label.clone(), point_label.clone())).ok_or(Error::Other(format!("evaluation of poly {} not found for point {}", label, point_label)))?;

                lc_value += (v_i - y_i) * cur_challenge * z_i_over_z_value;

                // lambda^i
                cur_challenge = cur_challenge * &lambda;
            }
        }

        // absorb evaluations of polynomials over x_point
        fs_rng.record::<G::BaseField, _>(field_elements_to_bits(values.iter()).as_slice())?;

        let values = values.into_iter().chain(vec![&lc_value]);

        sorted_commitments.push(&h_commitment);


        let res = Self::succinct_single_point_multi_poly_verify(vk, sorted_commitments, x_point, values, multi_point_proof.get_proof(), fs_rng);

        end_timer!(combine_time);

        res
    }

    /// The verifier for proofs generated by `fn multi_point_multi_poly_open()`.
    fn multi_point_multi_poly_verify<'a>(
        vk: &Self::VerifierKey,
        labeled_commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_map: &'a QueryMap<G::ScalarField>,
        evaluations: &Evaluations<G::ScalarField>,
        multi_point_proof: &Self::MultiPointProof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error> {
        let check_time = start_timer!(|| "Checking evaluations");

        let verifier_state = Self::succinct_multi_point_multi_poly_verify(
            vk,
            labeled_commitments,
            query_map,
            evaluations,
            multi_point_proof,
            fs_rng,
        )?;

        if verifier_state.is_none() {
            end_timer!(check_time);
            Err(Error::FailedSuccinctCheck)?
        }

        let res = Self::hard_verify(vk, &verifier_state.unwrap());

        end_timer!(check_time);

        res
    }

    /// Succinct verify (a batch of) multi-point multi-poly opening proofs and, if valid,
    /// return their SuccinctCheckPolynomials (the reduction challenges `xi`) and the
    /// final committer keys `GFinal`.
    fn batch_succinct_verify<'a>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a [LabeledCommitment<Self::Commitment>]>,
        query_maps: impl IntoIterator<Item = &'a QueryMap<'a, G::ScalarField>>,
        values: impl IntoIterator<Item = &'a Evaluations<'a, G::ScalarField>>,
        multi_point_proofs: impl IntoIterator<Item = &'a Self::MultiPointProof>,
        states: impl IntoIterator<Item = &'a <Self::RandomOracle as FiatShamirRng>::State>,
    ) -> Result<Vec<Self::VerifierState>, Self::Error>
    where
        Self::Commitment: 'a,
        Self::MultiPointProof: 'a,
        Self::RandomOracle: 'a,
    {
        let comms = commitments.into_iter().collect::<Vec<_>>();
        let query_maps = query_maps.into_iter().collect::<Vec<_>>();
        let values = values.into_iter().collect::<Vec<_>>();
        let multi_point_proofs = multi_point_proofs.into_iter().collect::<Vec<_>>();
        let states = states.into_iter().collect::<Vec<_>>();

        // Perform succinct verification of all the proofs and collect
        // the xi_s and the GFinal_s into DLogAccumulators
        let succinct_time = start_timer!(|| "Succinct verification of proofs");

        // TODO: into_par_iter should be used
        let (accumulators, failed_checks): (
            Vec<Result<_, Self::Error>>,
            Vec<Result<_, Self::Error>>,
        ) = comms
            .into_iter()
            .zip(query_maps)
            .zip(values)
            .zip(multi_point_proofs)
            .zip(states)
            .map(
                |((((commitments, query_map), values), multi_point_proof), state)| {
                    let mut fs_rng = Self::RandomOracle::default();
                    fs_rng.set_state(state.clone())?;

                    // Perform succinct check of i-th proof
                    let verifier_state = Self::succinct_multi_point_multi_poly_verify(
                        vk,
                        commitments,
                        query_map,
                        values,
                        multi_point_proof,
                        &mut fs_rng,
                    )?;

                    if verifier_state.is_none() {
                        Err(Error::FailedSuccinctCheck)?
                    }

                    Ok(verifier_state.unwrap())
                },
            )
            .partition(Result::is_ok);
        end_timer!(succinct_time);

        if !failed_checks.is_empty() {
            Err(Error::FailedSuccinctCheck)?
        }

        let accumulators = accumulators
            .into_iter()
            .map(Result::unwrap)
            .collect::<Vec<_>>();

        Ok(accumulators)
    }
}

/// Evaluate the given polynomials at `query_map` and returns a Vec<((poly_label, point_label), eval)>)
pub fn evaluate_query_map_to_vec<'a, F: Field>(
    polys: impl IntoIterator<Item = &'a LabeledPolynomial<F>>,
    query_map: &QueryMap<'a, F>,
) -> Vec<((String, String), F)> {
    let polys = BTreeMap::from_iter(polys.into_iter().map(|p| (p.label(), p)));
    let mut v = Vec::new();
    for (point_label, (point, poly_labels)) in query_map {
        for label in poly_labels {
            let poly = polys
                .get(label)
                .expect("polynomial in evaluated lc is not found");
            let eval = poly.evaluate(*point);
            v.push(((label.clone(), point_label.clone()), eval));
        }
    }
    v
}

/// Transform a challenge to its representation in the field F.
/// 'chal' bits are supposed to be in LE bit order.
pub(crate) fn read_fe_from_challenge<F: PrimeField>(mut chal: Vec<bool>) -> Result<F, Error> {
    // Pad before reversing if necessary
    if chal.len() < F::size_in_bits() {
        chal.append(&mut vec![false; F::size_in_bits() - chal.len()])
    }

    // Reverse and read (as read_bits read in BE)
    chal.reverse();
    let scalar = F::read_bits(chal).map_err(|e| Error::Other(e.to_string()))?;

    Ok(scalar)
}
