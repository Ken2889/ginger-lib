//!
//! A module for extending the domain of an arbitrary homomorphic commitment scheme beyond the
//! maximum degree supported by it.
mod constraints;
pub use constraints::*;
mod data_structures;
use algebra::EndoMulCurve;
pub use data_structures::*;

use crate::{Error, LinearCombination, Polynomial, PolynomialCommitment};
use crate::{PCCommitterKey, PCProof};
use algebra::{
    fields::Field,
    groups::{Group, GroupVec},
};
use digest::Digest;
use rand_core::RngCore;
use std::marker::PhantomData;

/// The domain extension of a given homomorphic commitment scheme `PC`.
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct DomainExtendedPolynomialCommitment<
    G: EndoMulCurve,
    PC: PolynomialCommitment<G, Commitment = G>,
> {
    _projective: PhantomData<G>,
    _pc: PhantomData<PC>,
}



// Domain extension beyond the maximum degree `s` is achieved by leveraging linearity.
// An (arbitrary degree) polynomial p(X) is regarded as sum of "segment polynomials", i.e.
//     p(X) = p_0(X) +  X^s * p_1(X) + ... +  X^{m*s} * p_m(X),
// with each of the "segment polynomials" p_i(X) of degree at most `s`, the maximum
// degree of the scheme. The commitment of p(X) is the vector of the commitments of its
// segment polynomials, and evaluation claims on p(X) are reduced to that of a query-point
// dependent linear combination of the p_i(X).
impl<G: EndoMulCurve, PC: 'static + PolynomialCommitment<G, Commitment = G>> PolynomialCommitment<G>
    for DomainExtendedPolynomialCommitment<G, PC>
{
    type Parameters = PC::Parameters;
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
    fn setup<D: Digest>(max_degree: usize) -> Result<Self::Parameters, Self::Error> {
        PC::setup::<D>(max_degree)
    }

    /// Setup of the base point vector (deterministically derived from the
    /// given byte array as seed).
    fn setup_from_seed<D: Digest>(
        max_degree: usize,
        seed: &[u8],
    ) -> Result<Self::Parameters, Self::Error> {
        PC::setup_from_seed::<D>(max_degree, seed)
    }

    fn commit(
        ck: &Self::CommitterKey,
        polynomial: &Polynomial<G::ScalarField>,
        is_hiding: bool,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Self::Commitment, Self::Randomness), Self::Error> {
        let rng = &mut crate::optional_rng::OptionalRng(rng);

        let key_len = ck.get_key_len();
        let p_len = polynomial.coeffs.len();
        let segments_count = std::cmp::max(
            1,
            p_len / key_len + if p_len % key_len != 0 { 1 } else { 0 },
        );

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
        let key_len = ck.get_key_len();

        if key_len.next_power_of_two() != key_len {
            Err(Error::Other(
                "Commiter key length is not power of 2".to_owned(),
            ))?
        }

        let lc_time = start_timer!(|| "LC of polynomial and randomness");

        let p_len = polynomial.coeffs.len();
        let segments_count = std::cmp::max(
            1,
            p_len / key_len + if p_len % key_len != 0 { 1 } else { 0 },
        );

        // Compute the query-point dependent linear combination of the segments,
        // both for witnesses, commitments (and their randomnesses, if hiding)

        let mut polynomials_lc = LinearCombination::<Polynomial<G::ScalarField>>::new(vec![]);
        let mut randomnesses_lc = LinearCombination::<PC::Randomness>::new(vec![]);

        let point_pow = point.pow(&[key_len as u64]);
        let mut coeff = G::ScalarField::one();

        for i in (0..segments_count).into_iter() {
            if i > 0 {
                coeff = coeff * &point_pow;
            }
            polynomials_lc.push(
                coeff.clone(),
                Polynomial::from_coefficients_slice(
                    &polynomial.coeffs[i * key_len..core::cmp::min((i + 1) * key_len, p_len)],
                ),
            );
            if is_hiding {
                // TODO: check the situation when poly has one segment more comparing to
                //  randomness segments
                randomnesses_lc.push(
                    coeff.clone(),
                    if randomness.len() <= i {
                        PC::Randomness::zero()
                    } else {
                        randomness[i].clone()
                    },
                );
            }
        }

        end_timer!(lc_time);

        PC::open_lc(
            ck,
            &polynomials_lc,
            point,
            is_hiding,
            &randomnesses_lc,
            fs_rng,
            rng,
        )
    }

    fn succinct_verify<'a>(
        vk: &Self::VerifierKey,
        combined_commitment: &'a Self::Commitment,
        point: G::ScalarField,
        value: G::ScalarField,
        proof: &Self::Proof,
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<Option<Self::VerifierState>, Self::Error> {
        let key_len = proof.get_key_len();

        let lc_time = start_timer!(|| "LC of segmented commitment");

        let point_pow = point.pow(&[key_len as u64]);
        let mut coeff = G::ScalarField::one();

        let commitments_lc = LinearCombination::<PC::Commitment>::new(
            combined_commitment
                .iter()
                .enumerate()
                .map(|(i, item)| {
                    if i > 0 {
                        coeff = coeff * &point_pow;
                    }
                    (coeff.clone(), item.clone())
                })
                .collect(),
        );

        end_timer!(lc_time);

        PC::succinct_verify_lc(vk, &commitments_lc, point, value, proof, fs_rng)
    }

    fn hard_verify(vk: &Self::VerifierKey, vs: &Self::VerifierState) -> Result<bool, Self::Error> {
        PC::hard_verify(vk, vs)
    }
}
