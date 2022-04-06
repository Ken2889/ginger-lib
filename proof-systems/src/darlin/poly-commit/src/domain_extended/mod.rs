//!
//! A module for extending the domain of an arbitrary homomorphic commitment scheme beyond the
//! maximum degree supported by it.
#[cfg(feature = "circuit-friendly")]
mod constraints;
#[cfg(feature = "circuit-friendly")]
pub use constraints::*;
mod data_structures;
pub use data_structures::*;

use crate::{LinearCombination, PCKey, PCProof, Polynomial, PolynomialCommitment};
use algebra::{
    fields::Field,
    groups::{Group, GroupVec},
};

use digest::Digest;
use num_traits::Zero;
use rand_core::RngCore;
use std::marker::PhantomData;

#[cfg(feature = "circuit-friendly")]
use crate::{LabeledCommitment, single_point_multi_poly_succinct_verify, LabeledPolynomial, LabeledRandomness, single_point_multi_poly_open};
#[cfg(feature = "circuit-friendly")]
use std::collections::{BTreeMap, BTreeSet, HashMap};
#[cfg(feature = "circuit-friendly")]
use crate::{Error, Evaluations, multi_point_multi_poly_open, QueryMap, succinct_multi_point_multi_poly_verify};


/*
This macro is employed both in the primitive and in the gadget to sort the inputs to functions for
single-point multi-poly proofs. The macro takes as input:
- A set $segmentized_items, which contains items each with possibly more than one segments; such
items are either segmentized polynomials or segmentized commitments,
depending on the macro being employed for single-point multi-poly open or verify functions, respectively
- A set $associated_data, which are in one-to-one correspondence with $segmentized_items;
such data are either the labeled randomnesses of the segmentized commitments or the evaluations
of the segmentized polynomials, depending on the macro being employed for single-point multi-poly
open or verify functions, respectively
- A closure $get_num_segments which, given an element of $segmentized_item, returns the number of
segments of the item
The macro iterates over $segmentized_items and their associated $data, sorting both collections in
ascending order on the number of segments. The label of the commitment is employed as a sorting
criteria for the polynomials with the same number of segments
*/
#[macro_export]
macro_rules! sort_according_to_segments {
    ($segmentized_items: ident, $associated_data: ident, $get_num_segments: tt) => {
        {
            // compute the number of items to check that all commitments/values are placed
            // in `sorted_collections`, as in case there are duplicates the `collect` on `BTreeMap`
            // just stops processing elements of the iterator rather than returning an error
            let segmentized_items_iter = $segmentized_items.into_iter();
            // check that the lower bound and upper bound on the iterator are the same and save its
            // value in `num_items` variable
            assert_eq!(segmentized_items_iter.size_hint().0, segmentized_items_iter.size_hint().1.unwrap());
            let num_items = segmentized_items_iter.size_hint().0;
            let sorted_collections = segmentized_items_iter.into_iter().zip($associated_data.into_iter()).map(|(item, data)| {
                (($get_num_segments(item), item.label()), (item, data))
            }).collect::<BTreeMap<(_, _), (_,_)>>();

            assert_eq!(num_items, sorted_collections.len());

            let (sorted_items, sorted_data): (Vec<_>, Vec<_>) = sorted_collections.into_iter().rev().map(|(_, (item, data))| (item, data)).unzip();
            (sorted_items, sorted_data)
        }
    }
}

/*
This macro is employed both in the primitive and in the gadget to implement functions for
multi-point multi-poly proofs which are optimized to process the commitments with an optimal order
according to their number of segments.
This macro takes the following input parameters:
- $multi_point_func is a closure which wraps the main function for multi-point multi-poly proof
 which is implemented by this macro (e.g., multi_point_multi_poly_open). The closure
 expects 2 input parameters
- $query_map is a QueryMap data structure, which maps a point (identified by its label) to the
set of polynomials (identified by their labels) which are evaluated over such points
- $polynomials is either a set of LabeledPolynomial or a set of LabeledCommitment, depending
on the multi_point_multi_poly function being implemented with the macro (i.e., if $multi_point_func
is an open (resp. verify) function, then polynomials is a set of LabeledPolynomial (resp. LabeledCommitment)
- $get_num_segments is a closure that, given as input an element of $polynomials
(i.e., either a LabeledPolynomial or a LabeledCommitment), compute the number of segments for such
polynomial/commitment
The macro first sorts $query_map as follows.
Each set of polynomials labels is sorted according to the number of segments of the polynomial/commitment;
the set of points is sorted according to the number of segments of the batch polynomial/commitment
of all the polynomials/commitments evaluated at the point at hand, which corresponds to the number
of segments of the polynomial/commitment with the largest number of segments in the set of
polynomials/commitments evaluated in each point.
Then, the macro invokes $multi_point_func providing a polynomial/commitment map, depending on the
function being called, and the sorted query map.
*/
#[macro_export]
#[cfg(feature = "circuit-friendly")]
macro_rules! multi_point_with_sorted_query_map {
    ($query_map: ident, $polynomials: ident, $get_num_segments: tt, $multi_point_func: tt) => {

        {
            let poly_map: HashMap<_, _> = $polynomials
                .into_iter()
                .map(|commitment| (commitment.label(), commitment))
                .collect();

            let mut sorted_query_map = BTreeMap::new();
            let mut values_for_sorted_map = Vec::with_capacity($query_map.len());
            for (point_label, (point, poly_labels)) in $query_map {
                let mut sorted_labels = BTreeSet::new();
                let mut max_segments = 0;
                for label in poly_labels {
                    let poly = *poly_map.get(label).ok_or(Error::MissingPolynomial {
                        label: label.to_string(),
                    })?;
                    let num_segments = $get_num_segments(poly);
                    sorted_labels.insert((num_segments, label.clone()));
                    if num_segments > max_segments {
                        max_segments = num_segments;
                    }
                }
                let sorted_labels_vec = sorted_labels.iter().rev().map(|(_, label)| label.clone() ).collect::<Vec<_>>();
                values_for_sorted_map.push((point.clone(), sorted_labels_vec));
                sorted_query_map.insert((max_segments, point_label), values_for_sorted_map.len()-1);
            }

            let sorted_query_map_vec = sorted_query_map.into_iter().rev().map(|((_, point_label), value)| (point_label, &values_for_sorted_map[value])).collect::<Vec<_>>();

            $multi_point_func(poly_map, sorted_query_map_vec)
        }
    }
}


fn compute_num_of_segments<G: Group, PC: PolynomialCommitment<G>>(
    ck: &PC::CommitterKey,
    polynomial: &Polynomial<G::ScalarField>,
) -> usize
{
    let key_len = ck.degree() + 1;

    let p_len = polynomial.coeffs.len();
    std::cmp::max(
        1,
        p_len / key_len + if p_len % key_len != 0 { 1 } else { 0 },
    )
}

/// The domain extension of a given homomorphic commitment scheme `PC`.
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct DomainExtendedPolynomialCommitment<G: Group, PC: PolynomialCommitment<G, Commitment = G>>
{
    _group: PhantomData<G>,
    _pc: PhantomData<PC>,
}

// Domain extension beyond the maximum degree `s` is achieved by leveraging linearity.
// An (arbitrary degree) polynomial p(X) is regarded as sum of "segment polynomials", i.e.
//     p(X) = p_0(X) +  X^s * p_1(X) + ... +  X^{m*s} * p_m(X),
// with each of the "segment polynomials" p_i(X) of degree at most `s`, the maximum
// degree of the scheme. The commitment of p(X) is the vector of the commitments of its
// segment polynomials, and evaluation claims on p(X) are reduced to that of a query-point
// dependent linear combination of the p_i(X).
impl<G: Group, PC: PolynomialCommitment<G, Commitment = G>> PolynomialCommitment<G>
    for DomainExtendedPolynomialCommitment<G, PC>
{
    type CommitterKey = PC::CommitterKey;
    type VerifierKey = PC::VerifierKey;
    type VerifierState = PC::VerifierState;
    type Commitment = GroupVec<PC::Commitment>;
    type Randomness = GroupVec<PC::Randomness>;
    type Proof = PC::Proof;
    type MultiPointProof = DomainExtendedMultiPointProof<G, PC::Proof>;
    type Error = PC::Error;
    type RandomOracle = PC::RandomOracle;

    /// Setup of the base point vector (deterministically derived from the
    /// PROTOCOL_NAME as seed).

    fn setup<D: Digest>(
        max_degree: usize,
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), Self::Error> {
        PC::setup::<D>(max_degree)
    }

    /// Setup of the base point vector (deterministically derived from the
    /// given byte array as seed).
    fn setup_from_seed<D: Digest>(
        max_degree: usize,
        seed: &[u8],
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), Self::Error> {
        PC::setup_from_seed::<D>(max_degree, seed)
    }

    fn commit(
        ck: &Self::CommitterKey,
        polynomial: &Polynomial<G::ScalarField>,
        is_hiding: bool,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Self::Commitment, Self::Randomness), Self::Error> {
        let key_len = ck.degree() + 1;

        let rng = &mut crate::optional_rng::OptionalRng(rng);
        let p_len = polynomial.coeffs.len();

        let segments_count = compute_num_of_segments::<G, PC>(ck, polynomial);

        let mut commitment = Self::Commitment::zero();
        let mut randomness = Self::Randomness::zero();

        // split the polynomial into segments and commit
        for i in 0..segments_count {
            let (commitment_item, randomness_item) = PC::commit(
                ck,
                &Polynomial::from_coefficients_slice(
                    &polynomial.coeffs[i * key_len..core::cmp::min((i + 1) * key_len, p_len)],
                ),
                is_hiding,
                Some(rng),
            )?;
            commitment.push(commitment_item);
            if is_hiding {
                randomness.push(randomness_item)
            }
        }

        Ok((commitment, randomness))
    }

    /// Evaluation proof for an arbitrary degree polynomial.
    /// Note: this default implementation demands that the state of the Fiat-Shamir
    /// rng is already bound to the evaluation claim (i.e. the commitment of the polynomial,
    /// the query point, and the value).
    fn open(
        ck: &Self::CommitterKey,
        polynomial: Polynomial<G::ScalarField>,
        point: G::ScalarField,
        is_hiding: bool,
        randomness: Self::Randomness,
        fs_rng: &mut Self::RandomOracle,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error> {
        let key_len = ck.degree() + 1;

        let lc_time = start_timer!(|| "LC of polynomial and randomness");

        let p_len = polynomial.coeffs.len();
        let segments_count = compute_num_of_segments::<G, PC>(ck, &polynomial);

        // Compute the query-point dependent linear combination of the segments,
        // both for witnesses, commitments (and their randomnesses, if hiding)

        let point_pow = point.pow(&[key_len as u64]);

        let mut raw_polys = Vec::new();
        let mut raw_rand_lc = Vec::new();
        for i in (0..segments_count).into_iter() {
            raw_polys.push(Polynomial::from_coefficients_slice(
                &polynomial.coeffs[i * key_len..core::cmp::min((i + 1) * key_len, p_len)],
            ));

            if is_hiding {
                // TODO: check the situation when poly has one segment more comparing to
                //  randomness segments
                raw_rand_lc.push(if randomness.len() <= i {
                    PC::Randomness::zero()
                } else {
                    randomness[i].clone()
                });
            }
        }

        end_timer!(lc_time);

        PC::open_lc(
            ck,
            LinearCombination::new_from_val(&point_pow, raw_polys.iter().collect()),
            point,
            is_hiding,
            LinearCombination::new_from_val(&point_pow, raw_rand_lc.iter().collect()),
            fs_rng,
            rng,
        )
    }

    fn succinct_verify(
        vk: &Self::VerifierKey,
        combined_commitment: &Self::Commitment,
        point: G::ScalarField,
        value: G::ScalarField,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<Option<Self::VerifierState>, Self::Error> {
        let log_key_len = proof.degree()? + 1;

        let lc_time = start_timer!(|| "LC of segmented commitment");

        let point_pow = point.pow(&[1 << log_key_len as u64]);

        let commitments_lc =
            LinearCombination::new_from_val(&point_pow, combined_commitment.iter().collect());

        end_timer!(lc_time);

        PC::succinct_verify_lc(vk, commitments_lc, point, value, proof, fs_rng)
    }

    fn hard_verify(vk: &Self::VerifierKey, vs: &Self::VerifierState) -> Result<bool, Self::Error> {
        PC::hard_verify(vk, vs)
    }

    fn challenge_to_scalar(chal: Vec<bool>) -> Result<G::ScalarField, Self::Error> {
        PC::challenge_to_scalar(chal)
    }

    #[cfg(feature = "circuit-friendly")]
    fn single_point_multi_poly_open<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item=&'a LabeledPolynomial<G::ScalarField>>,
        point: G::ScalarField,
        fs_rng: &mut Self::RandomOracle,
        labeled_randomnesses: impl IntoIterator<Item=&'a LabeledRandomness<Self::Randomness>>,
        rng: Option<&mut dyn RngCore>
    ) -> Result<Self::Proof, Self::Error> {
        /*
        Iterate over labeled polynomials and values, sorting them in ascending order
        on the number of segments. The label of the polynomial is employed as a sorting criteria
        for the polynomials with the same number of segments
        */

        // employ a counter to check that all polynomials/values are placed in `sorted_collections`,
        // as in case there are duplicates the `collect` on `BTreeMap`
        // just stops processing elements of the iterator rather than returning an error
        /*let mut counter = 0;
        let sorted_collections = labeled_polynomials.into_iter().zip(labeled_randomnesses.into_iter()).map(|(poly, rand)| {
            counter += 1;
            ((compute_num_of_segments::<G, PC>(ck, poly), poly.label()) , (poly, rand))
        }
        ).collect::<BTreeMap<(_, _), (_,_)>>();

        assert_eq!(counter, sorted_collections.len());

        let (sorted_polys, sorted_rands): (Vec<_>, Vec<_>) = sorted_collections.iter().rev().map(|(_, (poly, rand))| (poly, rand)).unzip();*/

        let (sorted_polys, sorted_rands) = sort_according_to_segments!(labeled_polynomials, labeled_randomnesses, (
            |poly| compute_num_of_segments::<G, PC>(ck, poly)
        ));

        single_point_multi_poly_open::<G, Self, _, _>(ck, sorted_polys, point, fs_rng, sorted_rands, rng)
    }

    #[cfg(feature = "circuit-friendly")]
    fn succinct_single_point_multi_poly_verify<'a>(
        vk: &Self::VerifierKey,
        labeled_commitments: impl IntoIterator<Item=&'a LabeledCommitment<Self::Commitment>>,
        point: G::ScalarField,
        values: impl IntoIterator<Item=&'a G::ScalarField>,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle) -> Result<Option<Self::VerifierState>, Self::Error> {

        let (sorted_commitments, sorted_values) = sort_according_to_segments!(labeled_commitments, values,
            (|comm: &LabeledCommitment<Self::Commitment>| comm.commitment().len()));

        single_point_multi_poly_succinct_verify::<G, Self, _, _>(vk, sorted_commitments, point, sorted_values, proof, fs_rng)
    }

    #[cfg(feature = "circuit-friendly")]
    fn multi_point_multi_poly_open<'b>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item=&'b LabeledPolynomial<G::ScalarField>>,
        query_map: &'b QueryMap<G::ScalarField>,
        fs_rng: &mut Self::RandomOracle,
        labeled_randomnesses: impl IntoIterator<Item=&'b LabeledRandomness<Self::Randomness>>,
        rng: Option<&mut dyn RngCore>) -> Result<Self::MultiPointProof, Self::Error> {
        /*let poly_map: HashMap<_, _> = labeled_polynomials
            .into_iter()
            .map(|poly| (poly.label(), poly))
            .collect();

        let (sorted_query_map, values_for_sorted_map) = sort_query_map!(query_map, poly_map, (|poly| compute_num_of_segments::<G, PC>(ck, poly)));

        let sorted_query_map_vec = sorted_query_map.into_iter().rev().map(|((_, point_label), value)| (point_label, &values_for_sorted_map[value])).collect::<Vec<_>>();

        multi_point_multi_poly_open::<G, Self, _, _, _>(
            ck,
            poly_map,
            sorted_query_map_vec,
            fs_rng,
            labeled_randomnesses,
            rng,
        )*/

        multi_point_with_sorted_query_map!(query_map, labeled_polynomials, (|poly| compute_num_of_segments::<G, PC>(ck, poly)),
            (|poly_map, sorted_query_map|
                multi_point_multi_poly_open::<G, Self, _, _, _>(
                ck,
                poly_map,
                sorted_query_map,
                fs_rng,
                labeled_randomnesses,
                rng,
                )
            )
        )
    }

    #[cfg(feature = "circuit-friendly")]
    fn succinct_multi_point_multi_poly_verify<'a>(
        vk: &Self::VerifierKey,
        labeled_commitments: impl IntoIterator<Item=&'a LabeledCommitment<Self::Commitment>>,
        query_map: &QueryMap<G::ScalarField>,
        evaluations: &Evaluations<G::ScalarField>,
        multi_point_proof: &Self::MultiPointProof,
        fs_rng: &mut Self::RandomOracle)
        -> Result<Option<Self::VerifierState>, Self::Error> {
        /*let commitment_map: HashMap<_, _> = labeled_commitments
            .into_iter()
            .map(|commitment| (commitment.label(), commitment))
            .collect();

        let (sorted_query_map, values_for_sorted_map) = sort_query_map!(query_map, commitment_map, (|comm: &LabeledCommitment<Self::Commitment>| comm.commitment().len()));

        let sorted_query_map_vec = sorted_query_map.into_iter().rev().map(|((_, point_label), value)| (point_label, &values_for_sorted_map[value])).collect::<Vec<_>>();*/

        multi_point_with_sorted_query_map!(query_map, labeled_commitments,
            (|comm: &LabeledCommitment<Self::Commitment>| comm.commitment().len()),
            (
                |comm_map, sorted_query_map|
                succinct_multi_point_multi_poly_verify::<G, Self, _, _ >(vk, comm_map, sorted_query_map, evaluations, multi_point_proof, fs_rng)
            )
        )

        //succinct_multi_point_multi_poly_verify::<G, Self, _, _ >(vk, commitment_map, sorted_query_map_vec, evaluations, multi_point_proof, fs_rng)
    }


}
