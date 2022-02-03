//!
//! Implements the `PolynomialCommitment` trait for the [BCMS20] scheme and some additional functions
//! related to batch verification of evalaution proofs:
//! * a "batch verifier" for the succinct parts of a batch of multi-point multi-poly opening proofs.
//! * a seperate aggregation prover for the verifier "hard" parts.
//!
//! [BCMS20]: https://eprint.iacr.org/2020/499
use crate::Error;
use crate::{Polynomial, PolynomialCommitment};
use crate::{ToString, Vec};
use algebra::msm::VariableBaseMSM;
use algebra::{
    BitIterator, Field, Group, PrimeField, SemanticallyValid, UniformRand, CanonicalSerialize, serialize_no_metadata, EndoMulCurve
};
use rand_core::RngCore;
use std::marker::PhantomData;
use std::{format, vec};

mod data_structures;
pub use data_structures::*;

use rayon::prelude::*;

use fiat_shamir::FiatShamirRng;
use digest::Digest;

#[cfg(test)]
mod tests;

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
/// The inner product argument from [BCMS20](https://eprint.iacr.org/2020/499).
pub struct InnerProductArgPC<G: EndoMulCurve, FS: FiatShamirRng> {
    _projective: PhantomData<G>,
    _fs: PhantomData<FS>,
}

impl<G: EndoMulCurve, FS: FiatShamirRng> InnerProductArgPC<G, FS> {
    /// `PROTOCOL_NAME` is used as a seed for the setup function.
    const PROTOCOL_NAME: &'static [u8] = b"PC-DL-BCMS-2020";

    #[inline]
    fn inner_product(l: &[G::ScalarField], r: &[G::ScalarField]) -> G::ScalarField {
        l.par_iter().zip(r).map(|(li, ri)| *li * ri).sum()
    }

    /// The low-level single segment single poly commit function.
    /// Create a dlog commitment to `scalars` using the commitment key `comm_key`.
    /// Optionally, randomize the commitment using `hiding_generator` and `randomizer`.
    pub fn inner_commit(
        comm_key: &[G::AffineRep],
        scalars: &[G::ScalarField],
        hiding_generator: Option<G>,
        randomizer: Option<G::ScalarField>,
    ) -> Result<G, Error> {
        let scalars_bigint = scalars
            .par_iter()
            .map(|s| s.into_repr())
            .collect::<Vec<_>>();
        let mut comm = VariableBaseMSM::multi_scalar_mul(comm_key, &scalars_bigint)
            .map_err(|e| Error::IncorrectInputLength(e.to_string()))?;
        if randomizer.is_some() {
            if hiding_generator.is_none() {
                return Err(Error::Other("Hiding generator is missing".to_owned()));
            }
            comm += &hiding_generator.unwrap().mul(&randomizer.unwrap());
        }
        Ok(comm)
    }

    /// Complete semantic checks on `ck`.
    #[inline]
    pub fn check_key<D: Digest>(ck: &CommitterKey<G>, max_degree: usize) -> bool {
        let pp = <Self as PolynomialCommitment<G>>::setup::<D>(max_degree).unwrap();
        ck.is_valid() && &pp.hash == &ck.hash
    }

    /// Perform a dlog reduction step as described in BCMS20
    fn round_reduce(
        round_challenge: G::ScalarField,
        round_challenge_inv: G::ScalarField,
        c_l: &mut [G::ScalarField],
        c_r: &[G::ScalarField],
        z_l: &mut [G::ScalarField],
        z_r: &[G::ScalarField],
        k_l: &mut [G],
        k_r: &[G::AffineRep],
    ) {
        c_l.par_iter_mut()
            .zip(c_r)
            .for_each(|(c_l, c_r)| *c_l += &(round_challenge_inv * c_r));

        z_l.par_iter_mut()
            .zip(z_r)
            .for_each(|(z_l, z_r)| *z_l += &(round_challenge * z_r));

        k_l.par_iter_mut().zip(k_r).for_each(|(k_l, k_r)| {
            *k_l += G::mul_bits_affine(&k_r, BitIterator::new(round_challenge.into_repr()))
        });
    }

    /// Computes an opening proof of multiple reduction polynomials `h(`xi`,X)` with a
    /// corresponding commitment `G_fin` opened at a challenge `point`.
    /// Used by a separate aggregation proof to optimize the verification of many
    /// dlog opening proofs in batch.
    /// Note: The entire opening assertions, i.e. the xi's and their G_fin's, are
    /// already bound the inner state of the Fiat-Shamir rng.
    // No segmentation here: Reduction polys are at most as big as the committer key.
    pub fn open_reduction_polynomials<'a>(
        ck: &CommitterKey<G>,
        xi_s: impl IntoIterator<Item = &'a SuccinctCheckPolynomial<G::ScalarField>>,
        point: G::ScalarField,
        // Assumption: the evaluation point and the (xi_s, g_fins) are already bound to the
        // fs_rng state.
        fs_rng: &mut FS,
    ) -> Result<Proof<G>, Error> {
        let mut key_len = ck.comm_key.len();
        if ck.comm_key.len().next_power_of_two() != key_len {
            return Err(Error::Other(
                "Commiter key length is not power of 2".to_owned(),
            ));
        }

        let batch_time = start_timer!(|| "Compute and batch Bullet Polys and GFin commitments");
        let xi_s_vec = xi_s.into_iter().collect::<Vec<_>>();

        // Compute the evaluations of the Bullet polynomials at point starting from the xi_s
        let values = xi_s_vec
            .par_iter()
            .map(|xi_s| xi_s.evaluate(point))
            .collect::<Vec<_>>();

        // Absorb evaluations
        fs_rng.absorb(values)?;

        // Sample new batching challenge
        let random_scalar = fs_rng.squeeze_128_bits_challenge::<G>();

        // Collect the powers of the batching challenge in a vector
        let mut batching_chal = G::ScalarField::one();
        let mut batching_chals = vec![G::ScalarField::zero(); xi_s_vec.len()];
        for i in 0..batching_chals.len() {
            batching_chals[i] = batching_chal;
            batching_chal *= &random_scalar;
        }

        // Compute combined check_poly
        let combined_check_poly = batching_chals
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
            ));
        }

        end_timer!(batch_time);

        Self::open(
            ck,
            combined_check_poly,
            point,
            false,
            G::ScalarField::zero(),
            fs_rng,
            None,
        )
    }

    /// Computing the base point vector of the commmitment scheme in a
    /// deterministic manner, given the PROTOCOL_NAME.
    fn sample_generators<D: Digest>(num_generators: usize, seed: &[u8]) -> Vec<G> {
        let generators: Vec<_> = (0..num_generators)
            .into_par_iter()
            .map(|i| {
                let i = i as u64;
                let mut hash = D::digest(&serialize_no_metadata![seed, i].unwrap());
                let mut g = G::from_random_bytes(&hash);
                let mut j = 0u64;
                while g.is_none() {
                    hash = D::digest(&serialize_no_metadata![seed, i, j].unwrap());
                    g = G::from_random_bytes(&hash);
                    j += 1;
                }
                let generator = g.unwrap();
                generator.scale_by_cofactor()
            })
            .collect();

        generators
    }
}

/// Implementation of the PolynomialCommitment trait for the BCMS scheme.
impl<G: EndoMulCurve, FS: FiatShamirRng> PolynomialCommitment<G> for InnerProductArgPC<G, FS> {
    type Parameters = Parameters<G>;
    type CommitterKey = CommitterKey<G>;
    type VerifierKey = VerifierKey<G>;
    // The succinct part of the verifier returns the dlog reduction challenges that
    // define the succinct check polynomial.
    type VerifierState = VerifierState<G>;
    type Commitment = G;
    type Randomness = G::ScalarField;
    type Proof = Proof<G>;
    type MultiPointProof = MultiPointProof<G>;
    type Error = Error;
    type RandomOracle = FS;

    /// Setup of the base point vector (deterministically derived from the
    /// PROTOCOL_NAME as seed).
    fn setup<D: Digest>(max_degree: usize) -> Result<Self::Parameters, Self::Error> {
        Self::setup_from_seed::<D>(max_degree, &Self::PROTOCOL_NAME)
    }

    /// Setup of the base point vector (deterministically derived from the
    /// given byte array as seed).
    fn setup_from_seed<D: Digest>(max_degree: usize, seed: &[u8]) -> Result<Self::Parameters, Self::Error> {
        // Ensure that max_degree + 1 is a power of 2
        let max_degree = (max_degree + 1).next_power_of_two() - 1;

        let setup_time = start_timer!(|| format!("Sampling {} generators", max_degree + 3));
        let generators = Self::sample_generators::<D>(max_degree + 3, seed);
        end_timer!(setup_time);

        let hash = D::digest(&serialize_no_metadata![&generators, max_degree as u32].unwrap()).to_vec();

        let h = generators[0].clone();
        let s = generators[1].clone();
        let comm_key = G::batch_normalization_into_affine(generators[2..].to_vec()).unwrap();

        let pp = Parameters {
            comm_key,
            h,
            s,
            hash,
        };

        Ok(pp)
    }

    fn commit(
        ck: &Self::CommitterKey,
        polynomial: &Polynomial<G::ScalarField>,
        is_hiding: bool,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<(Self::Commitment, Self::Randomness), Self::Error> {
        let rng = &mut crate::optional_rng::OptionalRng(rng);

        let randomness = if is_hiding {
            Self::Randomness::rand(rng)
        } else {
            Self::Randomness::zero()
        };

        let commitment = Self::inner_commit(
            ck.comm_key.as_slice(),
            &polynomial.coeffs,
            if is_hiding { Some(ck.s) } else { None },
            if is_hiding { Some(randomness) } else { None },
        )?;

        Ok((commitment, randomness))
    }

    fn open(
        ck: &Self::CommitterKey,
        polynomial: Polynomial<G::ScalarField>,
        point: G::ScalarField,
        is_hiding: bool,
        randomness: Self::Randomness,
        fs_rng: &mut Self::RandomOracle,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error> {
        let key_len = ck.comm_key.len();
        let log_key_len = algebra::log2(key_len) as usize;

        if key_len.next_power_of_two() != key_len {
            Err(Error::Other(
                "Commiter key length is not power of 2".to_owned(),
            ))?
        }

        let proof_time = start_timer!(|| format!(
            "Generating proof for degree {} combined polynomial",
            key_len
        ));

        let mut polynomial = polynomial;
        let mut rand = randomness;

        // The BCMS way to reduce a zk-opening proof to one which doesn't.
        // Instead of proving that `p(x) = y`, the prover commits a mask
        // polynomial `m(X)` s.t. `m(x) = 0`, and is required to open the
        // random linear combination
        //      `LC(p(X),m(X)) = p(X) + rho * m(X)`
        // to the value `y` instead.
        let hiding_comm = if is_hiding {
            let mut rng = rng.expect("hiding commitments require randomness");
            let hiding_time = start_timer!(|| "Applying hiding.");
            // sample a full-length mask polynomial `m(X)` so that `m(x) = 0`.
            let mut hiding_polynomial = Polynomial::rand(key_len - 1, &mut rng);
            hiding_polynomial -=
                &Polynomial::from_coefficients_slice(&[hiding_polynomial.evaluate(point)]);

            let (hiding_commitment, hiding_randomness) =
                Self::commit(ck, &hiding_polynomial, true, Some(rng))?;

            // We assume that the commitments, the query point, and the evaluations are already
            // bound to the internal state of the Fiat-Shamir rng. Hence the same is true for
            // the deterministically derived combined_commitment and its combined_v.
            fs_rng.absorb(hiding_commitment)?;
            // the random coefficient `rho`
            let hiding_challenge = fs_rng.squeeze_128_bits_challenge::<G>();

            // compute random linear combination using the hiding_challenge,
            // both for witnesses and commitments (and it's randomness)
            polynomial += (hiding_challenge, &hiding_polynomial);
            rand += &(hiding_challenge * &hiding_randomness);
            fs_rng.absorb(rand)?;

            end_timer!(hiding_time);

            Some(hiding_commitment)
        } else {
            None
        };

        let rand = if is_hiding { Some(rand) } else { None };

        // 0-th challenge
        let mut round_challenge = fs_rng.squeeze_128_bits_challenge::<G>();

        let h_prime = ck.h.mul(&round_challenge);

        // Pads the coefficients with zeroes to get the number of coeff to be key_len
        let mut coeffs = polynomial.coeffs.clone();
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
        let mut key_proj = G::batch_from_affine(&ck.comm_key);
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

            let l = Self::inner_commit(key_l, coeffs_r, None, None)?
                + &h_prime.mul(&Self::inner_product(coeffs_r, z_l));

            let r = Self::inner_commit(key_r, coeffs_l, None, None)?
                + &h_prime.mul(&Self::inner_product(coeffs_l, z_r));

            let lr = vec![l, r];
            l_vec.push(lr[0]);
            r_vec.push(lr[1]);

            // the previous challenge is bound to the internal state, hence
            // no need to absorb it
            fs_rng.absorb([lr[0], lr[1]])?;

            round_challenge = fs_rng.squeeze_128_bits_challenge::<G>();
            // round_challenge is guaranteed to be non-zero by squeeze function
            let round_challenge_inv = round_challenge.inverse().unwrap();

            Self::round_reduce(
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
            temp = G::batch_normalization_into_affine(key_proj.to_vec()).unwrap();
            comm_key = &temp;

            n /= 2;
        }

        end_timer!(proof_time);

        Ok(Proof {
            l_vec,
            r_vec,
            final_comm_key: G::from_affine(&comm_key[0]),
            c: coeffs[0],
            hiding_comm,
            rand,
        })
    }

    /// The "succinct" verifier of a proof produced by `fn open()`.
    /// Does all a full verifier does, except the correctness check of G_fin.
    fn succinct_verify(
        vk: &VerifierKey<G>,
        commitment: &Self::Commitment,
        point: G::ScalarField,
        value: G::ScalarField,
        proof: &Proof<G>,
        fs_rng: &mut FS,
    ) -> Result<Option<Self::VerifierState>, Self::Error> {
        let succinct_verify_time = start_timer!(|| "Succinct verify");

        let log_key_len = proof.l_vec.len();

        if proof.l_vec.len() != proof.r_vec.len() {
            end_timer!(succinct_verify_time);
            Err(Error::IncorrectInputLength(
                format!(
                    "expected l_vec size and r_vec size to be equal; instead l_vec size is {:} and r_vec size is {:}",
                    proof.l_vec.len(),
                    proof.r_vec.len()
                )
            ))?
        }

        // At the end combined_commitment_proj = C
        let mut combined_commitment_proj = commitment.clone();

        if proof.hiding_comm.is_some() != proof.rand.is_some() {
            end_timer!(succinct_verify_time);
            Err(Error::Other(
                "Hiding commitment and proof randomness must be both either present or not present"
                    .to_owned(),
            ))?
        }

        if proof.hiding_comm.is_some() {
            let hiding_comm = proof.hiding_comm.unwrap();
            let rand = proof.rand.unwrap();

            fs_rng.absorb(hiding_comm)?;
            let hiding_challenge = fs_rng.squeeze_128_bits_challenge::<G>();
            fs_rng.absorb(rand)?;

            combined_commitment_proj += &(hiding_comm.mul(&hiding_challenge) - &vk.s.mul(&rand));
        }

        // Challenge for each round
        let mut round_challenges = Vec::with_capacity(log_key_len);

        let mut round_challenge = fs_rng.squeeze_128_bits_challenge::<G>();

        let h_prime = vk.h.mul(&round_challenge);

        let mut round_commitment_proj = combined_commitment_proj + &h_prime.mul(&value);

        let l_iter = proof.l_vec.iter();
        let r_iter = proof.r_vec.iter();

        for (l, r) in l_iter.zip(r_iter) {
            fs_rng.absorb([*l, *r])?;
            round_challenge = fs_rng.squeeze_128_bits_challenge::<G>();

            round_challenges.push(round_challenge);

            // round_challenge is guaranteed to be non-zero by squeeze function
            round_commitment_proj +=
                &(l.mul(&round_challenge.inverse().unwrap()) + &r.mul(&round_challenge));
        }

        // check_poly = h(X) = prod (1 + xi_{log(d+1) - i} * X^{2^i} )
        let check_poly = SuccinctCheckPolynomial::<G::ScalarField>(round_challenges);
        let v_prime = check_poly.evaluate(point) * &proof.c;

        let check_commitment_elem: G = Self::inner_commit(
            &[
                proof.final_comm_key.into_affine().unwrap(),
                h_prime.into_affine().unwrap(),
            ],
            &[proof.c.clone(), v_prime],
            None,
            None,
        )?;

        if !G::is_zero(&(round_commitment_proj - &check_commitment_elem)) {
            end_timer!(succinct_verify_time);
            return Ok(None);
        }

        end_timer!(succinct_verify_time);

        Ok(Some(VerifierState {
            check_poly,
            final_comm_key: proof.final_comm_key,
        }))
    }

    /// The "hard", or non-succinct part of the verifier for a proof produced by `open()`.
    /// Does the remaining check of the "final committer key".
    fn hard_verify(vk: &Self::VerifierKey, vs: &Self::VerifierState) -> Result<bool, Self::Error> {
        let check_poly_time = start_timer!(|| "Compute check poly");
        let check_poly_coeffs = vs.check_poly.compute_coeffs();
        end_timer!(check_poly_time);

        let hard_time = start_timer!(|| "DLOG hard part");
        let final_key = Self::inner_commit(
            vk.comm_key.as_slice(),
            check_poly_coeffs.as_slice(),
            None,
            None,
        )?;
        end_timer!(hard_time);

        if !G::is_zero(&(final_key - &vs.final_comm_key)) {
            return Ok(false);
        }

        Ok(true)
    }
}
