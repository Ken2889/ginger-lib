use crate::{BTreeMap, String, ToString, Vec};
use crate::{Error, Evaluations, QuerySet};
use crate::{LabeledCommitment, LabeledPolynomial, LabeledRandomness};
use crate::{PCRandomness, PCUniversalParams, Polynomial, PolynomialCommitment};
use algebra::msm::VariableBaseMSM;
use algebra::{
    to_bytes, AffineCurve, Field, Group, PrimeField, ProjectiveCurve, SemanticallyValid, ToBytes,
    UniformRand,
};
use rand_core::RngCore;
use std::marker::PhantomData;
use std::{format, vec};

mod data_structures;
pub use data_structures::*;

use rayon::prelude::*;

use crate::rng::{FiatShamirChaChaRng, FiatShamirRng};
use digest::Digest;

/// The dlog commitment scheme from Bootle et al. based on the hardness of the discrete
/// logarithm problem in prime-order groups.
/// This implementation is according to the variant given in [[BCMS20]][pcdas], extended
/// to support polynomials of arbitrary degree via segmentation.
///
/// Degree bound enforcement requires that (at least one of) the points at
/// which a committed polynomial is evaluated are from a distribution that is
/// random conditioned on the polynomial. This is because degree bound
/// enforcement relies on checking a polynomial identity at this point.
/// More formally, the points must be sampled from an admissible query sampler,
/// as detailed in [[CHMMVW20]][marlin].
///
/// [pcdas]: https://eprint.iacr.org/2020/499
/// [marlin]: https://eprint.iacr.org/2019/1047
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct InnerProductArgPC<G: AffineCurve, D: Digest> {
    _projective: PhantomData<G>,
    _digest: PhantomData<D>,
}

impl<G: AffineCurve, D: Digest> InnerProductArgPC<G, D> {
    /// `PROTOCOL_NAME` is used as a seed for the setup function.
    const PROTOCOL_NAME: &'static [u8] = b"PC-DL-2021";

    /// The low-level single segment single poly commit function.
    /// Create a dlog commitment to `scalars` using the commitment key `comm_key`.
    /// Optionally, randomize the commitment using `hiding_generator` and `randomizer`.
    pub fn cm_commit(
        comm_key: &[G],
        scalars: &[G::ScalarField],
        hiding_generator: Option<G>,
        randomizer: Option<G::ScalarField>,
    ) -> Result<G::Projective, Error> {
        let scalars_bigint = scalars
            .par_iter()
            .map(|s| s.into_repr())
            .collect::<Vec<_>>();
        let mut comm = VariableBaseMSM::multi_scalar_mul(&comm_key, &scalars_bigint)
            .map_err(|e| Error::IncorrectInputLength(e.to_string()))?;
        if randomizer.is_some() {
            if hiding_generator.is_none() {
                return Err(Error::Other("Hiding generator is missing".to_owned()))
            }
            comm += &hiding_generator.unwrap().mul(randomizer.unwrap());
        }
        Ok(comm)
    }

    #[inline]
    fn inner_product(l: &[G::ScalarField], r: &[G::ScalarField]) -> G::ScalarField {
        l.par_iter().zip(r).map(|(li, ri)| *li * ri).sum()
    }

    /// Complete semantic checks on `ck`.
    #[inline]
    pub fn check_key(ck: &CommitterKey<G>, max_degree: usize) -> bool {
        let pp = <Self as PolynomialCommitment<G::ScalarField>>::setup(max_degree).unwrap();
        ck.is_valid() && &pp.hash == &ck.hash
    }

    /// Computes an opening proof of multiple check polynomials with a corresponding
    /// commitment GFin opened at point.
    /// No segmentation here: Bullet Polys are at most as big as the committer key.
    pub fn open_check_polys<'a>(
        ck: &CommitterKey<G>,
        xi_s: impl IntoIterator<Item = &'a SuccinctCheckPolynomial<G::ScalarField>>,
        point: G::ScalarField,
        // Assumption: the evaluation point and the (xi_s, g_fins) are already bound to the
        // fs_rng state.
        fs_rng: &mut FiatShamirChaChaRng<D>,
    ) -> Result<Proof<G>, Error> {
        let mut key_len = ck.comm_key.len();
        if ck.comm_key.len().next_power_of_two() != key_len {
            return Err(Error::Other(
                "Commiter key length is not power of 2".to_owned(),
            ))
        }

        let batch_time = start_timer!(|| "Compute and batch Bullet Polys and GFin commitments");
        let xi_s_vec = xi_s.into_iter().collect::<Vec<_>>();

        // Compute the evaluations of the Bullet polynomials at point starting from the xi_s
        let values = xi_s_vec
            .par_iter()
            .map(|xi_s| xi_s.evaluate(point))
            .collect::<Vec<_>>();

        // Absorb evaluations
        fs_rng.absorb(
            &values
                .iter()
                .flat_map(|val| to_bytes!(val).unwrap())
                .collect::<Vec<_>>(),
        );

        // Sample new batching challenge
        let random_scalar: G::ScalarField = fs_rng.squeeze_128_bits_challenge();

        // Collect the powers of the batching challenge in a vector
        let mut batching_chal = G::ScalarField::one();
        let mut batching_chals = vec![G::ScalarField::zero(); xi_s_vec.len()];
        for i in 0..batching_chals.len() {
            batching_chals[i] = batching_chal;
            batching_chal *= &random_scalar;
        }

        // Compute combined check_poly
        let mut combined_check_poly = batching_chals
            .into_par_iter()
            .zip(xi_s_vec)
            .map(|(chal, xi_s)| Polynomial::from_coefficients_vec(xi_s.compute_scaled_coeffs(chal)))
            .reduce(Polynomial::zero, |acc, poly| &acc + &poly);

        // It's not necessary to use the full length of the ck if all the Bullet Polys are smaller:
        // trim the ck if that's the case
        key_len = combined_check_poly.coeffs.len();
        if key_len.next_power_of_two() != key_len {
            return Err(Error::Other(
                "Combined check poly length is not a power of 2".to_owned(),
            ))
        }
        let mut comm_key = &ck.comm_key[..key_len];

        end_timer!(batch_time);

        let proof_time = start_timer!(|| format!(
            "Generating proof for degree {} combined polynomial",
            key_len
        ));

        // ith challenge
        let mut round_challenge: G::ScalarField = fs_rng.squeeze_128_bits_challenge();

        let h_prime = ck.h.mul(round_challenge).into_affine();

        let mut coeffs = combined_check_poly.coeffs.as_mut_slice();

        // Powers of z
        let mut z: Vec<G::ScalarField> = Vec::with_capacity(key_len);
        let mut cur_z: G::ScalarField = G::ScalarField::one();
        for _ in 0..key_len {
            z.push(cur_z);
            cur_z *= &point;
        }
        let mut z = z.as_mut_slice();

        // This will be used for transforming the key in each step
        let mut key_proj: Vec<G::Projective> =
            comm_key.iter().map(|x| (*x).into_projective()).collect();
        let mut key_proj = key_proj.as_mut_slice();

        let mut temp;

        let log_key_len = algebra::log2(key_len) as usize;
        let mut l_vec = Vec::with_capacity(log_key_len);
        let mut r_vec = Vec::with_capacity(log_key_len);

        let mut n = key_len;
        while n > 1 {
            let (coeffs_l, coeffs_r) = coeffs.split_at_mut(n / 2);
            let (z_l, z_r) = z.split_at_mut(n / 2);
            let (key_l, key_r) = comm_key.split_at(n / 2);
            let (key_proj_l, _) = key_proj.split_at_mut(n / 2);

            let l = Self::cm_commit(key_l, coeffs_r, None, None)?
                + &h_prime.mul(Self::inner_product(coeffs_r, z_l));

            let r = Self::cm_commit(key_r, coeffs_l, None, None)?
                + &h_prime.mul(Self::inner_product(coeffs_l, z_r));

            let lr = G::Projective::batch_normalization_into_affine(vec![l, r]);
            l_vec.push(lr[0]);
            r_vec.push(lr[1]);

            fs_rng.absorb(&to_bytes![lr[0], lr[1]].unwrap());
            round_challenge = fs_rng.squeeze_128_bits_challenge();

            // round_challenge is guaranteed to be non-zero by squeeze function
            let round_challenge_inv = round_challenge.inverse().unwrap();

            Self::polycommit_round_reduce(
                round_challenge,
                round_challenge_inv,
                coeffs_l,
                coeffs_r,
                z_l,
                z_r,
                key_proj_l,
                key_r,
            );

            coeffs = coeffs_l;
            z = z_l;

            key_proj = key_proj_l;
            temp = G::Projective::batch_normalization_into_affine(key_proj.to_vec());
            comm_key = &temp;

            n /= 2;
        }

        end_timer!(proof_time);

        Ok(Proof {
            l_vec,
            r_vec,
            final_comm_key: comm_key[0],
            c: coeffs[0],
            hiding_comm: None,
            rand: None,
        })
    }

    /// The succinct portion of verifying a multi-poly single-point opening proof.
    /// If successful, returns the (recomputed) reduction challenge.
    pub fn succinct_check<'a>(
        vk: &VerifierKey<G>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<G>>>,
        point: G::ScalarField,
        values: impl IntoIterator<Item = G::ScalarField>,
        proof: &Proof<G>,
        // This implementation assumes that the commitments, point and evaluations are
        // already bound to the internal state of the Fiat Shamir rng
        fs_rng: &mut FiatShamirChaChaRng<D>,
    ) -> Result<Option<SuccinctCheckPolynomial<G::ScalarField>>, Error> {
        let check_time = start_timer!(|| "Succinct checking");

        // We do not assume that the vk length is equal to the segment size.
        // Instead, we read the segment size from the proof L and Rs vectors (i.e. the number
        // of steps of the dlog reduction). Doing so allows us to easily verify
        // the dlog opening proofs produced by different size-restricted by means
        // of a single vk.
        let log_key_len = proof.l_vec.len();
        let key_len = 1 << log_key_len;

        if proof.l_vec.len() != proof.r_vec.len() {
            return Err(Error::IncorrectInputLength(
                format!(
                    "expected l_vec size and r_vec size to be equal; instead l_vec size is {:} and r_vec size is {:}",
                    proof.l_vec.len(),
                    proof.r_vec.len()
                )
            ));
        }

        let mut combined_commitment_proj = <G::Projective as ProjectiveCurve>::zero();
        let mut combined_v = G::ScalarField::zero();

        let lambda: G::ScalarField = fs_rng.squeeze_128_bits_challenge();
        let mut cur_challenge = G::ScalarField::one();

        let labeled_commitments = commitments.into_iter();
        let values = values.into_iter();

        for (labeled_commitment, value) in labeled_commitments.zip(values) {
            let label = labeled_commitment.label();
            let commitment = labeled_commitment.commitment();
            combined_v += &(cur_challenge * &value);

            let segments_count = commitment.comm.len();

            let mut comm_lc = <G::Projective as ProjectiveCurve>::zero();
            for (i, comm_single) in commitment.comm.iter().enumerate() {
                if i == 0 {
                    comm_lc = comm_single.into_projective();
                } else {
                    let is = i * key_len;
                    comm_lc += &comm_single.mul(point.pow(&[is as u64]));
                }
            }

            if cur_challenge == G::ScalarField::one() {
                combined_commitment_proj = comm_lc;
            } else {
                combined_commitment_proj += &comm_lc.mul(&cur_challenge);
            }

            cur_challenge *= &lambda;

            let degree_bound = labeled_commitment.degree_bound();

            // If the degree_bound is a multiple of the key_len then there is no need to prove the degree bound polynomial identity.
            let degree_bound_len = degree_bound.and_then(|degree_bound_len| {
                if (degree_bound_len + 1) % key_len != 0 {
                    Some(degree_bound_len + 1)
                } else {
                    None
                }
            });

            if degree_bound_len.is_some() != commitment.shifted_comm.is_some() {
                return Err(Error::Other("Degree bound and shifted commitment must be both either present or not present".to_owned()))
            }

            if let Some(degree_bound_len) = degree_bound_len {
                if Self::check_segments_and_bounds(
                    degree_bound.unwrap(),
                    segments_count,
                    key_len,
                    label.clone(),
                )
                .is_err()
                {
                    return Ok(None);
                }

                let shifted_degree_bound = degree_bound_len % key_len - 1;
                let shift = -point.pow(&[(key_len - shifted_degree_bound - 1) as u64]);
                combined_commitment_proj += &commitment.shifted_comm.unwrap().mul(cur_challenge);
                combined_commitment_proj +=
                    &commitment.comm[segments_count - 1].mul(cur_challenge * &shift);

                cur_challenge *= &lambda;
            }
        }

        if proof.hiding_comm.is_some() != proof.rand.is_some() {
            return Err(Error::Other(
                "Hiding commitment and proof randomness must be both either present or not present"
                    .to_owned(),
            ))
        }

        if proof.hiding_comm.is_some() {
            let hiding_comm = proof.hiding_comm.unwrap();
            let rand = proof.rand.unwrap();

            fs_rng.absorb(&to_bytes![hiding_comm].unwrap());
            let hiding_challenge: G::ScalarField = fs_rng.squeeze_128_bits_challenge();
            fs_rng.absorb(&(to_bytes![rand].unwrap()));

            combined_commitment_proj += &(hiding_comm.mul(hiding_challenge) - &vk.s.mul(rand));
        }

        // Challenge for each round
        let mut round_challenges = Vec::with_capacity(log_key_len);

        let mut round_challenge: G::ScalarField = fs_rng.squeeze_128_bits_challenge();

        let h_prime = vk.h.mul(round_challenge);

        let mut round_commitment_proj = combined_commitment_proj + &h_prime.mul(&combined_v);

        let l_iter = proof.l_vec.iter();
        let r_iter = proof.r_vec.iter();

        for (l, r) in l_iter.zip(r_iter) {
            fs_rng.absorb(&to_bytes![l, r].unwrap());
            round_challenge = fs_rng.squeeze_128_bits_challenge();

            round_challenges.push(round_challenge);

            // round_challenge is guaranteed to be non-zero by squeeze function
            round_commitment_proj +=
                &(l.mul(round_challenge.inverse().unwrap()) + &r.mul(round_challenge));
        }

        let check_poly = SuccinctCheckPolynomial::<G::ScalarField>(round_challenges);
        let v_prime = check_poly.evaluate(point) * &proof.c;
        let h_prime = h_prime.into_affine();

        let check_commitment_elem: G::Projective = Self::cm_commit(
            &[proof.final_comm_key, h_prime],
            &[proof.c, v_prime],
            None,
            None,
        )?;

        if !ProjectiveCurve::is_zero(&(round_commitment_proj - &check_commitment_elem)) {
            end_timer!(check_time);
            return Ok(None);
        }

        end_timer!(check_time);
        Ok(Some(check_poly))
    }

    /// Succinct check of a multi-point multi-poly opening proof from [[BDFG2020]](https://eprint.iacr.org/2020/081)
    /// If successful, returns the (recomputed) succinct check polynomial (the xi_s)
    /// and the GFinal.
    pub fn succinct_batch_check_individual_opening_challenges<'a>(
        vk: &VerifierKey<G>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Commitment<G>>>,
        query_set: &QuerySet<G::ScalarField>,
        values: &Evaluations<G::ScalarField>,
        batch_proof: &BatchProof<G>,
        // This implementation assumes that the commitments, query set and evaluations are already absorbed by the Fiat Shamir rng
        fs_rng: &mut FiatShamirChaChaRng<D>,
    ) -> Result<(SuccinctCheckPolynomial<G::ScalarField>, G), Error> {
        let commitment_map: BTreeMap<_, _> = commitments
            .into_iter()
            .map(|commitment| (commitment.label(), commitment))
            .collect();

        let batch_check_time = start_timer!(|| "Multi poly multi point batch check: succinct part");
        let evals_time = start_timer!(|| "Compute batched poly value");

        // lambda
        let lambda: G::ScalarField = fs_rng.squeeze_128_bits_challenge();
        let mut cur_challenge = G::ScalarField::one();

        // Fresh random challenge x
        fs_rng.absorb(&to_bytes![batch_proof.h_comm].unwrap());
        let x_point: G::ScalarField = fs_rng.squeeze_128_bits_challenge();

        // LC(C): reconstructed commitment to LC(p_1(X),p_2(X),...,p_m(X),h(X))
        let mut lc_comm = vec![];

        // Expected value wich LC(p_1(X),p_2(X),...,p_m(X),h(X)) opens to
        let mut lc_value = G::ScalarField::zero();

        for (label, (_point_label, point)) in query_set.iter() {
            // Assert x_point != x_1, ..., x_m
            if point == &x_point {
                end_timer!(evals_time);
                end_timer!(batch_check_time);
                return Err(Error::Other(
                    "Squeezed a challenge equal to one of the evaluation points".to_owned(),
                ));
            }

            let labeled_commitment =
                *commitment_map.get(label).ok_or(Error::MissingCommitment {
                    label: label.to_string(),
                })?;

            // y_i
            let y_i = *values
                .get(&(label.clone(), *point))
                .ok_or(Error::MissingEvaluation {
                    label: label.to_string(),
                })?;

            // (X - x_i)
            let x_polynomial =
                Polynomial::from_coefficients_slice(&[-(*point), G::ScalarField::one()]);

            // z_i(x)/z(x) = 1 / (x - x_i).
            // unwrap cannot fail as x-x_i is guaranteed to be non-zero.
            let z_i_over_z_value = x_polynomial.evaluate(x_point).inverse().unwrap();

            // LC(C) = SUM ( lambda^i * z_i(x)/z(x) * C_i )
            for (index, &comm_dash_segment) in
                labeled_commitment.commitment().comm.iter().enumerate()
            {
                if index == lc_comm.len() {
                    lc_comm.push(<G::Projective as ProjectiveCurve>::zero());
                }
                lc_comm[index] += &comm_dash_segment.mul(z_i_over_z_value * &cur_challenge);
            }

            lc_value += y_i * cur_challenge * z_i_over_z_value;

            // lambda^i
            cur_challenge *= &lambda;
        }

        // LC(C) = SUM ( lambda^i * z_i(x)/z(x) * C_i ) - C
        let lc_comm_affine = lc_comm
            .into_iter()
            .enumerate()
            .map(|(index, mut lc_comm_segment)| {
                let h_comm_segment = if batch_proof.h_comm.len() > index {
                    batch_proof.h_comm[index]
                } else {
                    G::zero()
                };
                lc_comm_segment.add_assign_mixed(&-h_comm_segment);
                lc_comm_segment.into_affine()
            })
            .collect::<Vec<_>>();

        // Expected open value added to the check
        let batch_values = vec![lc_value];

        // The reconstructed commitment to the LC polynomial put to the check
        let labeled_batch_commitment = LabeledCommitment::new(
            "LC".to_string(),
            Commitment {
                comm: lc_comm_affine,
                shifted_comm: None,
            },
            None,
        );
        let batch_commitments = vec![&labeled_batch_commitment]; // commitments;

        let proof = &batch_proof.proof;
        end_timer!(evals_time);

        let check_time = start_timer!(|| "Succinct check batched polynomial");

        let check_poly =
            Self::succinct_check(vk, batch_commitments, x_point, batch_values, proof, fs_rng)?;

        if check_poly.is_none() {
            end_timer!(check_time);
            end_timer!(batch_check_time);
            return Err(Error::FailedSuccinctCheck);
        }

        end_timer!(check_time);
        end_timer!(batch_check_time);

        Ok((check_poly.unwrap(), proof.final_comm_key))
    }

    /// Succinct verify (a batch of) multi-point mulit-poly opening proofs and, if valid,
    /// return their SuccinctCheckPolynomials (the reduction challenges `xi`) and the
    /// final committer keys `GFinal`.
    pub fn succinct_batch_check<'a>(
        vk: &VerifierKey<G>,
        commitments: impl IntoIterator<Item = &'a [LabeledCommitment<Commitment<G>>]>,
        query_sets: impl IntoIterator<Item = &'a QuerySet<'a, G::ScalarField>>,
        values: impl IntoIterator<Item = &'a Evaluations<'a, G::ScalarField>>,
        proofs: impl IntoIterator<Item = &'a BatchProof<G>>,
        states: impl IntoIterator<Item = &'a <FiatShamirChaChaRng<D> as FiatShamirRng>::State>,
    ) -> Result<(Vec<SuccinctCheckPolynomial<G::ScalarField>>, Vec<G>), Error>
    where
        D::OutputSize: 'a,
    {
        let comms = commitments.into_iter().collect::<Vec<_>>();
        let query_sets = query_sets.into_iter().collect::<Vec<_>>();
        let values = values.into_iter().collect::<Vec<_>>();
        let proofs = proofs.into_iter().collect::<Vec<_>>();
        let states = states.into_iter().collect::<Vec<_>>();

        // Perform succinct verification of all the proofs and collect
        // the xi_s and the GFinal_s into DLogAccumulators
        let succinct_time = start_timer!(|| "Succinct verification of proofs");

        let (accumulators, failed_checks): (Vec<Result<_, Error>>, Vec<Result<_, Error>>) = comms
            .into_par_iter()
            .zip(query_sets)
            .zip(values)
            .zip(proofs)
            .zip(states)
            .map(|((((commitments, query_set), values), proof), state)| {
                let mut fs_rng = FiatShamirChaChaRng::<D>::default();
                fs_rng.set_state(state.clone());

                // Perform succinct check of i-th proof
                let (challenges, final_comm_key) =
                    Self::succinct_batch_check_individual_opening_challenges(
                        vk,
                        commitments,
                        query_set,
                        values,
                        proof,
                        &mut fs_rng,
                    )?;

                Ok((final_comm_key, challenges))
            })
            .partition(Result::is_ok);
        end_timer!(succinct_time);

        if !failed_checks.is_empty() {
            return Err(Error::FailedSuccinctCheck)
        }

        let accumulators = accumulators
            .into_iter()
            .map(Result::unwrap)
            .collect::<Vec<_>>();

        let g_finals = accumulators
            .iter()
            .map(|(g_final, _)| *g_final)
            .collect::<Vec<_>>();
        let challenges = accumulators
            .into_iter()
            .map(|(_, xi_s)| xi_s)
            .collect::<Vec<_>>();

        Ok((challenges, g_finals))
    }

    /// Checks whether degree bounds are `situated' in the last segment of a polynomial
    /// TODO: Rename to check_bounds, or alternatively write a function that receives the
    ///       supposed degree, and which checks in addition whether the segment count is plausible.
    fn check_degrees_and_bounds(
        supported_degree: usize,
        p: &LabeledPolynomial<G::ScalarField>,
    ) -> Result<(), Error> {
        // We use segmentation, therefore we allow arbitrary degree polynomials: hence, the only
        // check that makes sense, is the bound being bigger than the degree of the polynomial.
        if let Some(bound) = p.degree_bound() {
            let p_len = p.polynomial().coeffs.len();
            let segment_len = supported_degree + 1;
            let segments_count = std::cmp::max(
                1,
                p_len / segment_len + if p_len % segment_len != 0 { 1 } else { 0 },
            );

            if bound < p.degree() {
                return Err(Error::IncorrectDegreeBound {
                    poly_degree: p.degree(),
                    degree_bound: bound,
                    supported_degree,
                    label: p.label().to_string(),
                });
            }

            return Self::check_segments_and_bounds(
                bound,
                segments_count,
                segment_len,
                p.label().to_string(),
            );
        }

        Ok(())
    }

    /// Checks if the degree bound is situated in the last segment.
    fn check_segments_and_bounds(
        bound: usize,
        segments_count: usize,
        segment_len: usize,
        label: String,
    ) -> Result<(), Error> {
        if (bound + 1) <= (segments_count - 1) * segment_len
            || (bound + 1) > segments_count * segment_len
        {
            return Err(Error::IncorrectSegmentedDegreeBound {
                degree_bound: bound,
                segments_count,
                segment_len,
                label,
            });
        }

        Ok(())
    }

    /// Computes the 'shifted' polynomial as needed for degree bound proofs.
    fn shift_polynomial(
        ck: &CommitterKey<G>,
        p: &Polynomial<G::ScalarField>,
        degree_bound: usize,
    ) -> Polynomial<G::ScalarField> {
        if p.is_zero() {
            Polynomial::zero()
        } else {
            let mut shifted_polynomial_coeffs =
                vec![G::ScalarField::zero(); ck.comm_key.len() - 1 - degree_bound];
            shifted_polynomial_coeffs.extend_from_slice(&p.coeffs);
            Polynomial::from_coefficients_vec(shifted_polynomial_coeffs)
        }
    }

    /// Computing the base point vector of the commmitment scheme in a
    /// deterministic manner, given the PROTOCOL_NAME.
    fn sample_generators(num_generators: usize, seed: &[u8]) -> Vec<G> {
        let generators: Vec<_> = (0..num_generators)
            .into_par_iter()
            .map(|i| {
                let i = i as u64;
                let mut hash = D::digest(&to_bytes![seed, i].unwrap());
                let mut g = G::from_random_bytes(&hash);
                let mut j = 0u64;
                while g.is_none() {
                    hash = D::digest(&to_bytes![seed, i, j].unwrap());
                    g = G::from_random_bytes(&hash);
                    j += 1;
                }
                let generator = g.unwrap();
                generator.mul_by_cofactor().into_projective()
            })
            .collect();

        G::Projective::batch_normalization_into_affine(generators)
    }

    /// Perform a dlog reduction step as described in BCMS20
    fn polycommit_round_reduce(
        round_challenge: G::ScalarField,
        round_challenge_inv: G::ScalarField,
        c_l: &mut [G::ScalarField],
        c_r: &[G::ScalarField],
        z_l: &mut [G::ScalarField],
        z_r: &[G::ScalarField],
        k_l: &mut [G::Projective],
        k_r: &[G],
    ) {
        c_l.par_iter_mut()
            .zip(c_r)
            .for_each(|(c_l, c_r)| *c_l += &(round_challenge_inv * c_r));

        z_l.par_iter_mut()
            .zip(z_r)
            .for_each(|(z_l, z_r)| *z_l += &(round_challenge * z_r));

        k_l.par_iter_mut()
            .zip(k_r)
            .for_each(|(k_l, k_r)| *k_l += &(k_r.mul(round_challenge)));
    }
}

/// Implementation of the PolynomialCommitment trait for the segmentized dlog commitment scheme
impl<G: AffineCurve, D: Digest> PolynomialCommitment<G::ScalarField> for InnerProductArgPC<G, D> {
    type UniversalParams = UniversalParams<G>;
    type CommitterKey = CommitterKey<G>;
    type VerifierKey = VerifierKey<G>;
    type PreparedVerifierKey = PreparedVerifierKey<G>;
    type Commitment = Commitment<G>;
    type PreparedCommitment = PreparedCommitment<G>;
    type Randomness = Randomness<G>;
    type Proof = Proof<G>;
    type BatchProof = BatchProof<G>;
    type Error = Error;
    type RandomOracle = FiatShamirChaChaRng<D>;

    /// Setup of the base point vector (deterministically derived from the
    /// PROTOCOL_NAME as seed).
    fn setup(max_degree: usize) -> Result<Self::UniversalParams, Self::Error> {
        Self::setup_from_seed(max_degree, &Self::PROTOCOL_NAME)
    }

    /// Setup of the base point vector (deterministically derived from the
    /// given byte array as seed).
    fn setup_from_seed(
        max_degree: usize,
        seed: &[u8],
    ) -> Result<Self::UniversalParams, Self::Error> {
        // Ensure that max_degree + 1 is a power of 2
        let max_degree = (max_degree + 1).next_power_of_two() - 1;

        let setup_time = start_timer!(|| format!("Sampling {} generators", max_degree + 3));
        let generators = Self::sample_generators(max_degree + 3, seed);
        end_timer!(setup_time);

        let hash = D::digest(&to_bytes![&generators, max_degree as u32].unwrap()).to_vec();

        let h = generators[0];
        let s = generators[1];
        let comm_key = generators[2..].to_vec();

        let pp = UniversalParams {
            comm_key,
            h,
            s,
            hash,
        };

        Ok(pp)
    }

    /// Trims the base point vector of the setup function to a custom segment size
    fn trim(
        pp: &Self::UniversalParams,
        // the segment size (TODO: let's rename it!)
        supported_degree: usize,
    ) -> Result<(Self::CommitterKey, Self::VerifierKey), Self::Error> {
        // Ensure that supported_degree + 1 is a power of two
        let supported_degree = (supported_degree + 1).next_power_of_two() - 1;
        if supported_degree > pp.max_degree() {
            return Err(Error::TrimmingDegreeTooLarge);
        }

        let trim_time =
            start_timer!(|| format!("Trimming to supported degree of {}", supported_degree));

        let ck = CommitterKey {
            comm_key: pp.comm_key[0..(supported_degree + 1)].to_vec(),
            h: pp.h,
            s: pp.s,
            max_degree: pp.max_degree(),
            hash: pp.hash.clone(),
        };

        let vk = VerifierKey {
            comm_key: pp.comm_key[0..(supported_degree + 1)].to_vec(),
            h: pp.h,
            s: pp.s,
            max_degree: pp.max_degree(),
            hash: pp.hash.clone(),
        };

        end_timer!(trim_time);

        Ok((ck, vk))
    }

    /// Domain extended commit function, outputs a `segmented commitment'
    /// to a polynomial, regardless of its degree.
    fn commit<'a>(
        ck: &Self::CommitterKey,
        polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<G::ScalarField>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<
        (
            Vec<LabeledCommitment<Self::Commitment>>,
            Vec<LabeledRandomness<Self::Randomness>>,
        ),
        Self::Error,
    > {
        let rng = &mut crate::optional_rng::OptionalRng(rng);
        let mut comms = Vec::new();
        let mut rands = Vec::new();

        let commit_time = start_timer!(|| "Committing to polynomials");
        for labeled_polynomial in polynomials {
            Self::check_degrees_and_bounds(ck.comm_key.len() - 1, labeled_polynomial)?;

            let polynomial = labeled_polynomial.polynomial();
            let label = labeled_polynomial.label();
            let hiding_bound = labeled_polynomial.hiding_bound();
            let degree_bound = labeled_polynomial.degree_bound();

            let single_commit_time = start_timer!(|| format!(
                "Polynomial {} of degree {}, degree bound {:?}, and hiding bound {:?}",
                label,
                polynomial.degree(),
                degree_bound,
                hiding_bound,
            ));

            let key_len = ck.comm_key.len();
            let p_len = polynomial.coeffs.len();
            let segments_count = std::cmp::max(
                1,
                p_len / key_len + if p_len % key_len != 0 { 1 } else { 0 },
            );

            let randomness = if hiding_bound.is_some() {
                Randomness::rand(segments_count, degree_bound.is_some(), rng)
            } else {
                Randomness::empty(segments_count)
            };

            let comm: Vec<G>;

            // split poly in segments and commit all of them without shifting
            comm = (0..segments_count)
                .into_iter()
                .map(|i| {
                    Ok(Self::cm_commit(
                        &ck.comm_key,
                        &polynomial.coeffs[i * key_len..core::cmp::min((i + 1) * key_len, p_len)],
                        Some(ck.s),
                        Some(randomness.rand[i]),
                    )?
                    .into_affine())
                })
                .collect::<Result<Vec<_>, _>>()?;

            // committing only last segment shifted to the right edge
            let shifted_comm = if degree_bound.is_some() {
                let degree_bound = degree_bound.unwrap();
                let degree_bound_len = degree_bound + 1; // Convert to the maximum number of coefficients
                if degree_bound_len % key_len != 0 {
                    let comm = Self::cm_commit(
                        &ck.comm_key[key_len - (degree_bound_len % key_len)..],
                        &polynomial.coeffs[(segments_count - 1) * key_len..p_len],
                        Some(ck.s),
                        randomness.shifted_rand,
                    )?
                    .into_affine();
                    Some(comm)
                } else {
                    None
                }
            } else {
                None
            };

            let commitment = Commitment { comm, shifted_comm };
            let labeled_comm = LabeledCommitment::new(label.to_string(), commitment, degree_bound);
            let labeled_rand = LabeledRandomness::new(label.to_string(), randomness);

            comms.push(labeled_comm);
            rands.push(labeled_rand);

            end_timer!(single_commit_time);
        }

        end_timer!(commit_time);
        Ok((comms, rands))
    }

    /// Single point multi poly open, allowing the random oracle to be passed from
    /// 'outside' to the function.
    /// CAUTION: This is a low-level function which assumes that the statement of the
    /// opening proof (i.e. commitments, query point, and evaluations) is already bound
    /// to the internal state of the Fiat-Shamir rng.
    fn open_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<G::ScalarField>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: G::ScalarField,
        // This implementation assumes that commitments, query point and evaluations are already absorbed by the Fiat Shamir rng
        fs_rng: &mut Self::RandomOracle,
        rands: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error>
    where
        Self::Commitment: 'a,
        Self::Randomness: 'a,
    {
        let key_len = ck.comm_key.len();
        let log_key_len = algebra::log2(key_len) as usize;

        if key_len.next_power_of_two() != key_len {
            return Err(Error::Other(
                "Commiter key length is not power of 2".to_owned(),
            ))
        }

        let mut combined_polynomial = Polynomial::zero();
        let mut combined_rand = G::ScalarField::zero();
        let mut combined_commitment_proj = <G::Projective as ProjectiveCurve>::zero();

        let mut has_hiding = false;

        let polys_iter = labeled_polynomials.into_iter();
        let rands_iter = rands.into_iter();
        let comms_iter = commitments.into_iter();

        let combine_time = start_timer!(|| "Combining polynomials, randomness, and commitments.");

        // as the statement of the opening proof is already bound to the interal state of the fr_rng,
        // we simply squeeze the challenge scalar for the random linear combination
        let lambda: G::ScalarField = fs_rng.squeeze_128_bits_challenge();
        let mut cur_challenge = G::ScalarField::one();

        // compute the random linear combination using the powers of lambda
        for (labeled_polynomial, (labeled_commitment, labeled_randomness)) in
            polys_iter.zip(comms_iter.zip(rands_iter))
        {
            let label = labeled_polynomial.label();
            if labeled_polynomial.label() != labeled_commitment.label() {
                return Err(Error::Other(
                    format!(
                        "Labels are not equal: poly '{}'. commitment '{}'",
                        labeled_polynomial.label(),
                        labeled_commitment.label()
                    )
                    .to_owned(),
                ))
            }
            Self::check_degrees_and_bounds(ck.comm_key.len() - 1, labeled_polynomial)?;

            let polynomial = labeled_polynomial.polynomial();
            let degree_bound = labeled_polynomial.degree_bound();
            let hiding_bound = labeled_polynomial.hiding_bound();
            let commitment = labeled_commitment.commitment();
            let randomness = labeled_randomness.randomness();

            let p_len = polynomial.coeffs.len();
            let segments_count = std::cmp::max(
                1,
                p_len / key_len + if p_len % key_len != 0 { 1 } else { 0 },
            );

            // If the degree_bound is a multiple of the key_len then there is no need to prove the degree bound polynomial identity.
            let degree_bound_len = degree_bound.and_then(|degree_bound| {
                if (degree_bound + 1) % key_len != 0 {
                    Some(degree_bound + 1)
                } else {
                    None
                }
            });

            if degree_bound_len.is_some() != commitment.shifted_comm.is_some() {
                return Err(Error::Other(
                    format!("shifted_comm mismatch for {}", label).to_owned(),
                ))
            }

            if degree_bound != labeled_commitment.degree_bound() {
                return Err(Error::Other(
                    format!("labeled_comm degree bound mismatch for {}", label).to_owned(),
                ))
            }

            if hiding_bound.is_some() {
                has_hiding = true;
            }

            let mut polynomial_lc = Polynomial::zero();
            let mut comm_lc = <G::Projective as ProjectiveCurve>::zero();
            let mut rand_lc = G::ScalarField::zero();

            // Compute the query-point dependent linear combination of the segments,
            // both for witnesses, commitments (and their randomnesses, if hiding)
            for i in 0..segments_count {
                let is = i * key_len;
                let poly_single = Polynomial::from_coefficients_slice(
                    &polynomial.coeffs[i * key_len..core::cmp::min((i + 1) * key_len, p_len)],
                );
                let comm_single = commitment.comm[i];
                // add x^{i*|S|}* p_i(X) of the segment polynomial p_i(X)
                polynomial_lc += (point.pow(&[is as u64]), &poly_single);
                comm_lc += &comm_single.mul(point.pow(&[is as u64]));
                if has_hiding {
                    let rand_single = randomness.rand[i];
                    rand_lc += &(point.pow(&[is as u64]) * &rand_single);
                }
            }

            // add segment linear combination to overall combination,
            // both for witnesses, commitments (and their randomnesses, if hiding)
            combined_polynomial += (cur_challenge, &polynomial_lc);
            combined_commitment_proj += &comm_lc.mul(&cur_challenge);
            if has_hiding {
                combined_rand += &(cur_challenge * &rand_lc);
            }

            // next power of lambda
            cur_challenge *= &lambda;

            // If we prove degree bound, we add the degree bound identity
            //  p_shift(X) - x^{|S|-d} p(X),
            // where p(X) is the last segment polynomial, d its degree, |S| the
            // segment size and p_shift(X) the shifted polynomial.
            if let Some(degree_bound_len) = degree_bound_len {
                // degree bound relative to the last segment
                let shifted_degree_bound = degree_bound_len % key_len - 1;
                let last_segment_polynomial = Polynomial::from_coefficients_slice(
                    &polynomial.coeffs[(segments_count - 1) * key_len..p_len],
                );
                let shifted_polynomial =
                    Self::shift_polynomial(ck, &last_segment_polynomial, shifted_degree_bound);
                let shift = -point.pow(&[(key_len - shifted_degree_bound - 1) as u64]);

                // add the shifted polynomial p_shift(X) and its commitment
                combined_polynomial += (cur_challenge, &shifted_polynomial);
                combined_commitment_proj += &commitment.shifted_comm.unwrap().mul(cur_challenge);

                // add -x^{N-d} * p(X) and its commitment
                combined_polynomial += (cur_challenge * &shift, &last_segment_polynomial);
                combined_commitment_proj +=
                    &commitment.comm[segments_count - 1].mul(cur_challenge * &shift);

                // add the randomnesses accordingly
                if hiding_bound.is_some() {
                    let shifted_rand = randomness.shifted_rand;
                    if shifted_rand.is_none() {
                        return Err(Error::Other(
                            format!("shifted_rand.is_none() for {}", label).to_owned(),
                        ))
                    }
                    // randomness of p_shift(X)
                    combined_rand += &(cur_challenge * &shifted_rand.unwrap());
                    // randomness of -x^{N-d} * p(X)
                    combined_rand +=
                        &(cur_challenge * &shift * &randomness.rand[segments_count - 1]);
                }

                // next power of lamba
                cur_challenge *= &lambda;
            }
        }

        end_timer!(combine_time);

        let mut hiding_commitment = None;

        if has_hiding {
            let mut rng = rng.expect("hiding commitments require randomness");
            let hiding_time = start_timer!(|| "Applying hiding.");
            let mut hiding_polynomial = Polynomial::rand(key_len - 1, &mut rng);
            hiding_polynomial -=
                &Polynomial::from_coefficients_slice(&[hiding_polynomial.evaluate(point)]);

            let hiding_rand = G::ScalarField::rand(rng);
            let hiding_commitment_proj = Self::cm_commit(
                ck.comm_key.as_slice(),
                hiding_polynomial.coeffs.as_slice(),
                Some(ck.s),
                Some(hiding_rand),
            )?;

            let mut batch = G::Projective::batch_normalization_into_affine(vec![
                combined_commitment_proj,
                hiding_commitment_proj,
            ]);
            hiding_commitment = Some(batch.pop().unwrap());

            // We assume that the commitments, the query point, and the evaluations are already
            // bound to the internal state of the Fiat-Shamir rng. Hence the same is true for
            // the deterministically derived combined_commitment and its combined_v.
            fs_rng.absorb(&to_bytes![hiding_commitment.unwrap()].unwrap());
            let hiding_challenge: G::ScalarField = fs_rng.squeeze_128_bits_challenge();

            // compute random linear combination using the hiding_challenge,
            // both for witnesses and commitments (and it's randomness)
            combined_polynomial += (hiding_challenge, &hiding_polynomial);
            combined_rand += &(hiding_challenge * &hiding_rand);
            fs_rng.absorb(&to_bytes![combined_rand].unwrap());
            combined_commitment_proj +=
                &(hiding_commitment_proj.mul(&hiding_challenge) - &ck.s.mul(combined_rand));

            end_timer!(hiding_time);
        }

        let combined_rand = if has_hiding {
            Some(combined_rand)
        } else {
            None
        };

        let proof_time = start_timer!(|| format!(
            "Generating proof for degree {} combined polynomial",
            key_len
        ));

        // 0-th challenge
        let mut round_challenge: G::ScalarField = fs_rng.squeeze_128_bits_challenge();

        let h_prime = ck.h.mul(round_challenge).into_affine();

        // Pads the coefficients with zeroes to get the number of coeff to be key_len
        let mut coeffs = combined_polynomial.coeffs;
        if coeffs.len() < key_len {
            for _ in coeffs.len()..key_len {
                coeffs.push(G::ScalarField::zero());
            }
        }
        let mut coeffs = coeffs.as_mut_slice();

        // Powers of z
        let mut z: Vec<G::ScalarField> = Vec::with_capacity(key_len);
        let mut cur_z: G::ScalarField = G::ScalarField::one();
        for _ in 0..key_len {
            z.push(cur_z);
            cur_z *= &point;
        }
        let mut z = z.as_mut_slice();

        // This will be used for transforming the key in each step
        let mut key_proj: Vec<G::Projective> =
            ck.comm_key.iter().map(|x| (*x).into_projective()).collect();
        let mut key_proj = key_proj.as_mut_slice();

        let mut temp;

        // Key for MSM
        // We initialize this to capacity 0 initially because we want to use the key slice first
        let mut comm_key = &ck.comm_key;

        let mut l_vec = Vec::with_capacity(log_key_len);
        let mut r_vec = Vec::with_capacity(log_key_len);

        let mut n = key_len;
        while n > 1 {
            let (coeffs_l, coeffs_r) = coeffs.split_at_mut(n / 2);
            let (z_l, z_r) = z.split_at_mut(n / 2);
            let (key_l, key_r) = comm_key.split_at(n / 2);
            let (key_proj_l, _) = key_proj.split_at_mut(n / 2);

            let l = Self::cm_commit(key_l, coeffs_r, None, None)?
                + &h_prime.mul(Self::inner_product(coeffs_r, z_l));

            let r = Self::cm_commit(key_r, coeffs_l, None, None)?
                + &h_prime.mul(Self::inner_product(coeffs_l, z_r));

            let lr = G::Projective::batch_normalization_into_affine(vec![l, r]);
            l_vec.push(lr[0]);
            r_vec.push(lr[1]);

            // the previous challenge is bound to the internal state, hence
            // no need to absorb it
            fs_rng.absorb(&to_bytes![lr[0], lr[1]].unwrap());

            round_challenge = fs_rng.squeeze_128_bits_challenge();
            // round_challenge is guaranteed to be non-zero by squeeze function
            let round_challenge_inv = round_challenge.inverse().unwrap();

            Self::polycommit_round_reduce(
                round_challenge,
                round_challenge_inv,
                coeffs_l,
                coeffs_r,
                z_l,
                z_r,
                key_proj_l,
                key_r,
            );

            coeffs = coeffs_l;
            z = z_l;

            key_proj = key_proj_l;
            temp = G::Projective::batch_normalization_into_affine(key_proj.to_vec());
            comm_key = &temp;

            n /= 2;
        }

        end_timer!(proof_time);

        Ok(Proof {
            l_vec,
            r_vec,
            final_comm_key: comm_key[0],
            c: coeffs[0],
            hiding_comm: hiding_commitment,
            rand: combined_rand,
        })
    }

    /// The multi point multi poly opening proof from [[BDFG2020]](https://eprint.iacr.org/2020/081)
    /// CAUTION: This is a low-level function which assumes that the statement of the
    /// opening proof (i.e. commitments, query point, and evaluations) is already bound
    /// to the internal state of the Fiat-Shamir rng.
    fn batch_open_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<G::ScalarField>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<G::ScalarField>,
        // This implementation assumes that the commitments (as well as the query set and evaluations)
        // are already absorbed by the Fiat Shamir rng
        fs_rng: &mut Self::RandomOracle,
        rands: impl IntoIterator<Item = &'a LabeledRandomness<Self::Randomness>>,
        mut rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::BatchProof, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
    {
        let poly_map: BTreeMap<_, _> = labeled_polynomials
            .into_iter()
            .map(|poly| (poly.label(), poly))
            .collect();

        let rands_map: BTreeMap<_, _> =
            rands.into_iter().map(|rand| (rand.label(), rand)).collect();

        let commitment_map: BTreeMap<_, _> = commitments
            .into_iter()
            .map(|commitment| (commitment.label(), commitment))
            .collect();

        let batch_time = start_timer!(|| "Multi poly multi point batching.");

        // as the statement of the opening proof is already bound to the interal state of the fs_rng,
        // we simply squeeze the challenge scalar for the random linear combination
        let lambda: G::ScalarField = fs_rng.squeeze_128_bits_challenge();
        let mut cur_challenge = G::ScalarField::one();

        let mut has_hiding = false;

        let h_poly_time = start_timer!(|| "Compute h(X) polynomial");

        // h(X)
        let mut h_polynomial = Polynomial::zero();

        // z(X)
        let mut z_polynomial = Polynomial::from_coefficients_slice(&[G::ScalarField::one()]);

        // Save evaluation points for later
        let mut eval_points = std::collections::HashSet::new();

        for (label, (_point_label, point)) in query_set.iter() {
            eval_points.insert(point);
            let labeled_polynomial = *poly_map.get(label).ok_or(Error::MissingPolynomial {
                label: label.to_string(),
            })?;

            if labeled_polynomial.hiding_bound().is_some() {
                has_hiding = true;
            }

            // y_i
            let y_i = labeled_polynomial.polynomial().evaluate(*point);

            // (X - x_i)
            let x_polynomial =
                Polynomial::from_coefficients_slice(&[-(*point), G::ScalarField::one()]);

            // z(X) = PROD (X - x_i)
            z_polynomial = z_polynomial.naive_mul(&x_polynomial);

            // (p_i(X) - y_i) / (X - x_i)
            let polynomial = &(labeled_polynomial.polynomial()
                - &Polynomial::from_coefficients_slice(&[y_i]))
                / &x_polynomial;

            // h(X) = SUM( lambda^i * ((p_i(X) - y_i) / (X - x_i)) )
            h_polynomial += (cur_challenge, &polynomial);

            // lambda^i
            cur_challenge *= &lambda;
        }

        end_timer!(h_poly_time);

        let commit_time = start_timer!(|| format!(
            "Commit to h(X) polynomial of degree {}",
            h_polynomial.degree()
        ));

        let (h_commitments, h_randomnesses) = Self::commit(
            &ck,
            vec![&LabeledPolynomial::new(
                "h_poly".to_string(),
                h_polynomial.clone(),
                None,
                if has_hiding { Some(1) } else { None },
            )],
            if has_hiding {
                if rng.is_none() {
                    return Err(Error::Other("Rng not set".to_owned()))
                }
                Some(rng.as_mut().unwrap())
            } else {
                None
            },
        )?;

        let h_comm = h_commitments[0].commitment().comm.clone();
        let h_randomness = h_randomnesses[0].randomness();

        end_timer!(commit_time);

        let open_time = start_timer!(|| "Open LC(p_1(X),p_2(X),...,p_m(X),h(X)) polynomial");

        // Fresh random challenge x for multi-point to single-point reduction.
        // Except the `batch_commitment`, all other commitments are already bound
        // to the internal state of the Fiat-Shamir
        fs_rng.absorb(&to_bytes![h_comm].unwrap());
        let x_point: G::ScalarField = fs_rng.squeeze_128_bits_challenge();

        // Assert x_point != x_1, ..., x_m
        if eval_points
            .into_iter()
            .any(|eval_point| eval_point == &x_point)
        {
            end_timer!(open_time);
            end_timer!(batch_time);
            return Err(Error::Other(
                "Squeezed a challenge equal to one of the evaluation points".to_owned(),
            ));
        }

        // LC(p_1(X),p_2(X),...,p_m(X),h(X))
        let mut lc_polynomial = Polynomial::zero();
        let mut lc_randomness = Randomness::empty(0);

        // LC(C): reconstructed commitment to LC(p_1(X),p_2(X),...,p_m(X),h(X))
        let mut lc_comm = vec![];

        let mut cur_challenge = G::ScalarField::one();

        for (label, (_point_label, point)) in query_set.iter() {
            let labeled_polynomial = *poly_map.get(label).ok_or(Error::MissingPolynomial {
                label: label.to_string(),
            })?;

            let labeled_commitment =
                *commitment_map.get(label).ok_or(Error::MissingCommitment {
                    label: label.to_string(),
                })?;

            let labeled_randomness = *rands_map.get(label).ok_or(Error::MissingRandomness {
                label: label.to_string(),
            })?;

            // (X - x_i)
            let x_polynomial =
                Polynomial::from_coefficients_slice(&[-(*point), G::ScalarField::one()]);

            // z_i(x)/z(x) = 1 / (x - x_i).
            // unwrap cannot fail as x-x_i is guaranteed to be non-zero.
            let z_i_over_z_value = x_polynomial.evaluate(x_point).inverse().unwrap();

            // LC(p_1(X),p_2(X),...,p_m(X)) = SUM ( lamda^i * z_i(x)/z(x) * p_i(X) )
            lc_polynomial += (
                cur_challenge * z_i_over_z_value,
                labeled_polynomial.polynomial(),
            );

            // LC(C) = SUM ( lambda^i * z_i(x)/z(x) * C_i )
            for (index, &comm_dash_segment) in
                labeled_commitment.commitment().comm.iter().enumerate()
            {
                if index == lc_comm.len() {
                    lc_comm.push(<G::Projective as ProjectiveCurve>::zero());
                }
                lc_comm[index] += &comm_dash_segment.mul(z_i_over_z_value * &cur_challenge);
            }

            if has_hiding {
                for (index, &rand_segment) in
                    labeled_randomness.randomness().rand.iter().enumerate()
                {
                    if index == lc_randomness.rand.len() {
                        lc_randomness.rand.push(G::ScalarField::zero());
                    }
                    lc_randomness.rand[index] += rand_segment * cur_challenge * z_i_over_z_value;
                }
            }

            // lambda^i
            cur_challenge *= &lambda;
        }

        // z(x)
        // let z_x_value = z_polynomial.evaluate(x_point);

        // LC(p_1(X),p_2(X),...,p_m(X),h(X)) = SUM ( lamda^i * z_i(x)/z(x) * p_i(X) ) -  h(X)
        lc_polynomial -= &h_polynomial;

        // LC(C) = SUM ( lambda^i * z_i(x)/z(x) * C_i ) - * C
        let lc_comm_affine = lc_comm
            .into_iter()
            .enumerate()
            .map(|(index, mut lc_comm_segment)| {
                let h_comm_segment = if h_comm.len() > index {
                    h_comm[index]
                } else {
                    G::zero()
                };
                lc_comm_segment.add_assign_mixed(&-h_comm_segment);
                lc_comm_segment.into_affine()
            })
            .collect::<Vec<_>>();

        if has_hiding {
            for (index, &rand_segment) in h_randomness.rand.iter().enumerate() {
                if index == lc_randomness.rand.len() {
                    lc_randomness.rand.push(G::ScalarField::zero());
                }
                lc_randomness.rand[index] += -rand_segment;
            }
        }

        // TODO: after optimization we have only one polynomial, so this is actually
        //       single poly single point opening
        //       should be taken into account during the refactoring

        // LC(p_1(X),p_2(X),...,p_m(X),h(X)) polynomial added to the set of polynomials for multi-poly single-point batching
        let labeled_batch_polynomial = LabeledPolynomial::new(
            "LC".to_string(),
            lc_polynomial,
            None,
            if has_hiding { Some(1) } else { None },
        );
        let labeled_polynomials = vec![&labeled_batch_polynomial];

        // Commitment to LC(p_1(X),p_2(X),...,p_m(X),h(X)) polynomial added to the set of polynomials for multi-poly single-point batching
        let labeled_batch_commitment = LabeledCommitment::new(
            "LC".to_string(),
            Commitment {
                comm: lc_comm_affine,
                shifted_comm: None,
            },
            None,
        );
        let batch_commitments = vec![&labeled_batch_commitment]; // commitments;

        let labeled_batch_rand = LabeledRandomness::new("LC".to_string(), lc_randomness);
        let rands = vec![&labeled_batch_rand];

        let proof = Self::open_individual_opening_challenges(
            ck,
            labeled_polynomials,
            batch_commitments,
            x_point,
            fs_rng,
            rands,
            rng,
        )?;
        end_timer!(open_time);

        end_timer!(batch_time);

        Ok(BatchProof { proof, h_comm })
    }

    /// The verification function of an opening proof produced by ``open_individual_opening_challenges()``
    fn check_individual_opening_challenges<'a>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: G::ScalarField,
        values: impl IntoIterator<Item = G::ScalarField>,
        proof: &Self::Proof,
        // This implementation assumes that the commitments, point and evaluations are already absorbed by the Fiat Shamir rng
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error>
    where
        Self::Commitment: 'a,
    {
        let check_time = start_timer!(|| "Checking evaluations");

        let check_poly = Self::succinct_check(vk, commitments, point, values, proof, fs_rng)?;

        if check_poly.is_none() {
            return Ok(false);
        }

        let check_poly_time = start_timer!(|| "Compute check poly");
        let check_poly_coeffs = check_poly.unwrap().compute_coeffs();
        end_timer!(check_poly_time);

        let hard_time = start_timer!(|| "DLOG hard part");
        let final_key = Self::cm_commit(
            vk.comm_key.as_slice(),
            check_poly_coeffs.as_slice(),
            None,
            None,
        )?;
        end_timer!(hard_time);

        if !ProjectiveCurve::is_zero(&(final_key - &proof.final_comm_key.into_projective())) {
            end_timer!(check_time);
            return Ok(false);
        }

        end_timer!(check_time);
        Ok(true)
    }

    /// Verifies a multi-point multi-poly opening proof from [[BDFG2020]](https://eprint.iacr.org/2020/081).
    fn batch_check_individual_opening_challenges<'a>(
        vk: &Self::VerifierKey,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<G::ScalarField>,
        evaluations: &Evaluations<G::ScalarField>,
        batch_proof: &Self::BatchProof,
        // This implementation assumes that commitments, query set and evaluations are already absorbed by the Fiat Shamir rng
        fs_rng: &mut Self::RandomOracle,
    ) -> Result<bool, Self::Error>
    where
        Self::Commitment: 'a,
    {
        // DLOG "succinct" part
        let (check_poly, proof_final_key) =
            Self::succinct_batch_check_individual_opening_challenges(
                vk,
                commitments,
                query_set,
                evaluations,
                batch_proof,
                fs_rng,
            )?;

        // DLOG hard part
        let check_time = start_timer!(|| "DLOG hard part");
        let check_poly_coeffs = check_poly.compute_coeffs();
        let final_key = Self::cm_commit(
            vk.comm_key.as_slice(),
            check_poly_coeffs.as_slice(),
            None,
            None,
        )?;
        if !ProjectiveCurve::is_zero(&(final_key - &proof_final_key.into_projective())) {
            end_timer!(check_time);
            return Ok(false);
        }

        end_timer!(check_time);
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_camel_case_types)]

    use super::InnerProductArgPC;
    use crate::Error;

    use crate::rng::{
        FiatShamirChaChaRng, FiatShamirChaChaRngSeed, FiatShamirRng, FiatShamirRngSeed,
    };
    use crate::{PCCommitterKey, PCUniversalParams, PolynomialCommitment};
    use algebra::{
        curves::tweedle::dee::{Affine, Projective},
        to_bytes, ToBytes,
    };
    use blake2::Blake2s;
    use digest::Digest;

    type PC<E, D> = InnerProductArgPC<E, D>;
    type PC_DEE = PC<Affine, Blake2s>;

    #[test]
    fn constant_poly_test() {
        use crate::tests::*;
        constant_poly_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
    }

    #[test]
    fn constant_poly_negative_test() {
        use crate::tests::*;
        match constant_poly_test::<_, PC_DEE>(Some(NegativeType::Values)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match constant_poly_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match constant_poly_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match constant_poly_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
    }

    #[test]
    fn single_poly_test() {
        use crate::tests::*;
        single_poly_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
    }

    #[test]
    fn single_poly_negative_test() {
        use crate::tests::*;
        match single_poly_test::<_, PC_DEE>(Some(NegativeType::Values)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
    }

    #[test]
    fn quadratic_poly_degree_bound_multiple_queries_test() {
        use crate::tests::*;
        quadratic_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(None)
            .expect("test failed for tweedle_dee-blake2s");
    }

    #[test]
    fn quadratic_poly_degree_bound_multiple_queries_negative_test() {
        use crate::tests::*;
        match quadratic_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(Some(
            NegativeType::Values,
        )) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match quadratic_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(Some(
            NegativeType::Commitments,
        )) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match quadratic_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(Some(
            NegativeType::CommitterKey,
        )) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match quadratic_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(Some(
            NegativeType::VerifierKey,
        )) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
    }

    #[test]
    fn two_poly_four_points_test() {
        use crate::tests::*;
        two_poly_four_points_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
    }

    #[test]
    fn two_poly_four_points_negative_test() {
        use crate::tests::*;
        match two_poly_four_points_test::<_, PC_DEE>(Some(NegativeType::Values)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match two_poly_four_points_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match two_poly_four_points_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match two_poly_four_points_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
    }

    #[test]
    fn linear_poly_degree_bound_test() {
        use crate::tests::*;
        linear_poly_degree_bound_test::<_, PC_DEE>(None)
            .expect("test failed for tweedle_dee-blake2s");
    }

    #[test]
    fn linear_poly_degree_bound_negative_test() {
        use crate::tests::*;
        match linear_poly_degree_bound_test::<_, PC_DEE>(Some(NegativeType::Values)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match linear_poly_degree_bound_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match linear_poly_degree_bound_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match linear_poly_degree_bound_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
    }

    #[test]
    fn single_poly_degree_bound_test() {
        use crate::tests::*;
        single_poly_degree_bound_test::<_, PC_DEE>(None)
            .expect("test failed for tweedle_dee-blake2s");
    }

    #[test]
    fn single_poly_degree_bound_negative_test() {
        use crate::tests::*;
        match single_poly_degree_bound_test::<_, PC_DEE>(Some(NegativeType::Values)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_degree_bound_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_degree_bound_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_degree_bound_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
    }

    #[test]
    fn single_poly_degree_bound_multiple_queries_test() {
        use crate::tests::*;
        single_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(None)
            .expect("test failed for tweedle_dee-blake2s");
    }

    #[test]
    fn single_poly_degree_bound_multiple_queries_negative_test() {
        use crate::tests::*;
        match single_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(Some(
            NegativeType::Values,
        )) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(Some(
            NegativeType::Commitments,
        )) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(Some(
            NegativeType::CommitterKey,
        )) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match single_poly_degree_bound_multiple_queries_test::<_, PC_DEE>(Some(
            NegativeType::VerifierKey,
        )) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
    }

    #[test]
    fn two_polys_degree_bound_single_query_test() {
        use crate::tests::*;
        two_polys_degree_bound_single_query_test::<_, PC_DEE>(None)
            .expect("test failed for tweedle_dee-blake2s");
    }

    #[test]
    fn two_polys_degree_bound_single_query_negative_test() {
        use crate::tests::*;
        match two_polys_degree_bound_single_query_test::<_, PC_DEE>(Some(NegativeType::Values)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match two_polys_degree_bound_single_query_test::<_, PC_DEE>(Some(NegativeType::Commitments))
        {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match two_polys_degree_bound_single_query_test::<_, PC_DEE>(Some(
            NegativeType::CommitterKey,
        )) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match two_polys_degree_bound_single_query_test::<_, PC_DEE>(Some(NegativeType::VerifierKey))
        {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
    }

    #[test]
    fn full_end_to_end_test() {
        use crate::tests::*;
        full_end_to_end_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
        println!("Finished tweedle_dee-blake2s");
    }

    #[test]
    fn full_end_to_end_negative_test() {
        use crate::tests::*;
        match full_end_to_end_test::<_, PC_DEE>(Some(NegativeType::Values)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match full_end_to_end_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match full_end_to_end_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match full_end_to_end_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        println!("Finished tweedle_dee-blake2s");
    }

    #[test]
    fn segmented_test() {
        use crate::tests::*;
        segmented_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
        println!("Finished tweedle_dee-blake2s");
    }

    #[test]
    fn segmented_negative_test() {
        use crate::tests::*;
        match segmented_test::<_, PC_DEE>(Some(NegativeType::Values)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match segmented_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
            Err(Error::FailedSuccinctCheck) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match segmented_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        match segmented_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
            Err(Error::IncorrectProof) => {}
            Ok(_) => {
                panic!("test should fail for tweedle_dee-blake2s")
            }
            Err(e) => {
                panic!("test failed for tweedle_dee-blake2s: {:?}", e)
            }
        };
        println!("Finished tweedle_dee-blake2s");
    }

    // #[test]
    // fn single_equation_test() {
    //     use crate::tests::*;
    //     single_equation_test::<_, PC_DEE>(false).expect("test failed for tweedle_dee-blake2s");
    //     println!("Finished tweedle_dee-blake2s");
    // }
    //
    // #[test]
    // fn two_equation_test() {
    //     use crate::tests::*;
    //     two_equation_test::<_, PC_DEE>(false).expect("test failed for tweedle_dee-blake2s");
    //     println!("Finished tweedle_dee-blake2s");
    // }
    //
    // #[test]
    // fn two_equation_degree_bound_test() {
    //     use crate::tests::*;
    //     two_equation_degree_bound_test::<_, PC_DEE>(false)
    //         .expect("test failed for tweedle_dee-blake2s");
    //     println!("Finished tweedle_dee-blake2s");
    // }
    //
    // #[test]
    // fn full_end_to_end_equation_test() {
    //     use crate::tests::*;
    //     full_end_to_end_equation_test::<_, PC_DEE>(false)
    //         .expect("test failed for tweedle_dee-blake2s");
    //     println!("Finished tweedle_dee-blake2s");
    // }

    #[test]
    #[should_panic]
    fn bad_degree_bound_test() {
        use crate::tests::*;
        bad_degree_bound_test::<_, PC_DEE>().expect("test failed for tweedle_dee-blake2s");
        println!("Finished tweedle_dee-blake2s");
    }

    #[test]
    fn key_hash_test() {
        let max_degree = 1 << 7;
        let supported_degree = 1 << 5;

        let pp = PC_DEE::setup(max_degree).unwrap();
        let (ck, _) = PC_DEE::trim(&pp, supported_degree).unwrap();

        assert!(PC_DEE::check_key(&ck, max_degree));
        assert!(!PC_DEE::check_key(&ck, supported_degree));
        assert!(ck.get_hash() == pp.get_hash());

        let h =
            Blake2s::digest(&to_bytes![&ck.comm_key, &ck.h, &ck.s, ck.max_degree as u32].unwrap())
                .to_vec();
        assert_ne!(h.as_slice(), ck.get_hash());
    }

    #[test]
    fn fiat_shamir_rng_test() {
        use algebra::fields::tweedle::fr::Fr;
        use algebra::UniformRand;

        // Empty test
        {
            let mut rng1 = FiatShamirChaChaRng::<Blake2s>::from_seed(
                FiatShamirChaChaRngSeed::default().finalize(),
            );
            let mut rng2 = FiatShamirChaChaRng::<Blake2s>::default();

            assert_eq!(rng1.get_state(), rng2.get_state());

            let a = Fr::rand(&mut rng1);
            let b = Fr::rand(&mut rng2);

            assert_eq!(a, b);
            assert_eq!(rng1.get_state(), rng2.get_state());

            rng1.absorb(b"ABSORBABLE_ELEM");
            rng2.absorb(b"ABSORBABLE_ELEM");

            assert_eq!(rng1.get_state(), rng2.get_state());

            let a: Fr = rng1.squeeze_128_bits_challenge();
            let b: Fr = rng2.squeeze_128_bits_challenge();

            assert_eq!(a, b);
            assert_eq!(rng1.get_state(), rng2.get_state());
        }

        // No cross protocol attacks possible
        {
            let fs_rng_seed = {
                let mut seed_builder = FiatShamirChaChaRngSeed::new();
                seed_builder.add_bytes(b"TEST_SEED").unwrap();
                seed_builder.finalize()
            };

            let malicious_fs_rng_seed = {
                let mut seed_builder = FiatShamirChaChaRngSeed::new();
                seed_builder.add_bytes(b"TEST_").unwrap();
                seed_builder.add_bytes(b"SEED").unwrap();
                seed_builder.finalize()
            };

            let mut fs_rng = FiatShamirChaChaRng::<Blake2s>::from_seed(fs_rng_seed);
            let mut malicious_fs_rng =
                FiatShamirChaChaRng::<Blake2s>::from_seed(malicious_fs_rng_seed);

            assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

            let a = Fr::rand(&mut fs_rng);
            let b = Fr::rand(&mut malicious_fs_rng);

            assert_ne!(a, b);
            assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

            fs_rng.absorb(b"ABSORBABLE_ELEM");
            malicious_fs_rng.absorb(b"ABSORBABLE_ELEM");

            assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

            let a: Fr = fs_rng.squeeze_128_bits_challenge();
            let b: Fr = malicious_fs_rng.squeeze_128_bits_challenge();

            assert_ne!(a, b);
            assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());
        }

        // set_state test
        {
            let fs_rng_seed = {
                let mut seed_builder = FiatShamirChaChaRngSeed::new();
                seed_builder.add_bytes(b"TEST_SEED").unwrap();
                seed_builder.finalize()
            };
            let mut fs_rng = FiatShamirChaChaRng::<Blake2s>::from_seed(fs_rng_seed);

            let mut fs_rng_copy = FiatShamirChaChaRng::<Blake2s>::default();
            fs_rng_copy.set_state(*fs_rng.get_state());

            assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());

            fs_rng.absorb(b"ABSORBABLE_ELEM");
            fs_rng_copy.absorb(b"ABSORBABLE_ELEM");

            assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());

            let a: Fr = fs_rng.squeeze_128_bits_challenge();
            let b: Fr = fs_rng_copy.squeeze_128_bits_challenge();

            assert_eq!(a, b);
            assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());
        }
    }

    #[test]
    fn polycommit_round_reduce_test() {
        use algebra::fields::tweedle::fr::Fr;
        use algebra::{AffineCurve, Field, ProjectiveCurve, UniformRand};
        use rayon::prelude::*;

        let mut rng = &mut rand::thread_rng();

        let round_challenge = Fr::rand(&mut rng);
        let round_challenge_inv = round_challenge.inverse().unwrap();

        let samples = 1 << 10;

        let mut coeffs_l = (0..samples).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

        let coeffs_r = (0..samples).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

        let mut z_l = (0..samples).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

        let z_r = (0..samples).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

        let mut key_proj_l = (0..samples)
            .map(|_| Projective::rand(&mut rng))
            .collect::<Vec<_>>();

        let key_r = (0..samples)
            .map(|_| Projective::rand(&mut rng).into_affine())
            .collect::<Vec<_>>();

        let mut gpu_coeffs_l = coeffs_l.clone();
        let gpu_coeffs_r = coeffs_r.clone();
        let mut gpu_z_l = z_l.clone();
        let gpu_z_r = z_r.clone();
        let mut gpu_key_proj_l = key_proj_l.clone();
        let gpu_key_r = key_r.clone();

        coeffs_l
            .par_iter_mut()
            .zip(coeffs_r)
            .for_each(|(c_l, c_r)| *c_l += &(round_challenge_inv * &c_r));

        z_l.par_iter_mut()
            .zip(z_r)
            .for_each(|(z_l, z_r)| *z_l += &(round_challenge * &z_r));

        key_proj_l
            .par_iter_mut()
            .zip(key_r)
            .for_each(|(k_l, k_r)| *k_l += &k_r.mul(round_challenge));

        PC_DEE::polycommit_round_reduce(
            round_challenge,
            round_challenge_inv,
            &mut gpu_coeffs_l,
            &gpu_coeffs_r,
            &mut gpu_z_l,
            &gpu_z_r,
            &mut gpu_key_proj_l,
            &gpu_key_r,
        );

        assert_eq!(coeffs_l, gpu_coeffs_l);
        assert_eq!(z_l, gpu_z_l);
        assert_eq!(key_proj_l, gpu_key_proj_l);
    }
}
