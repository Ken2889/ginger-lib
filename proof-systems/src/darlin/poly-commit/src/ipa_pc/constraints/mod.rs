use crate::ipa_pc::constraints::data_structures::{
    BulletPolynomial, IPAMultiPointProof, IPAProofGadget, IPAVerifierKeyGadget, IPAVerifierState,
};
use crate::ipa_pc::InnerProductArgPC;
use crate::{Error, PolynomialCommitmentVerifierGadget};
use algebra::{EndoMulCurve, Field, PrimeField};
use fiat_shamir::constraints::FiatShamirRngGadget;
use fiat_shamir::FiatShamirRng;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::groups::EndoMulCurveGadget;
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use r1cs_std::{FromBitsGadget, ToBitsGadget};
use std::marker::PhantomData;
use rand::thread_rng;
use r1cs_std::boolean::Boolean;

mod data_structures;

#[cfg(feature = "circuit-friendly")]
#[cfg(test)]
mod tests;

pub(crate) fn safe_mul<'a, ConstraintF, G, GG, CS, IT>(
    mut cs: CS,
    base_point: &GG,
    scalar: IT,
    endo_mul: bool,
) -> Result<GG, SynthesisError>
    where
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF> + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,

        CS: ConstraintSystemAbstract<ConstraintF>,
        IT: Iterator<Item = &'a Boolean>,
{
    let rng = &mut thread_rng();
    let mut non_trivial_base_constant = G::rand(rng);
    while non_trivial_base_constant.is_zero() {
        non_trivial_base_constant = G::rand(rng);
    }
    let non_trivial_base_gadget = GG::from_value(
        cs.ns(|| "alloc non trivial base constant"),
        &non_trivial_base_constant,
    );
    let zero = GG::zero(cs.ns(|| "alloc constant 0"))?;

    let is_zero = base_point.is_zero(cs.ns(|| "check if base point is zero"))?;
    let non_trivial_base_point = GG::conditionally_select(
        cs.ns(|| "select non trivial base point for mul"),
        &is_zero,
        &non_trivial_base_gadget,
        &base_point,
    )?;
    let safe_mul_res = if endo_mul {
        non_trivial_base_point.endo_mul(
            cs.ns(|| "base_point*scalar"),
            scalar.cloned().collect::<Vec<_>>().as_slice(),
        )
    } else {
        non_trivial_base_point.mul_bits(cs.ns(|| "base_point*scalar"), scalar)
    }?;
    GG::conditionally_select(
        cs.ns(|| "select correct result for safe mul"),
        &is_zero,
        &zero,
        &safe_mul_res,
    )
}

/// poly-commit verifier gadget implementation from the inner-product argument ([BCMS20](https://eprint.iacr.org/2020/499))
pub struct InnerProductArgGadget<ConstraintF: PrimeField, FSG: FiatShamirRngGadget<ConstraintF>, G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF> + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>> {
    _constraint_field_phantom: PhantomData<ConstraintF>,
    _fiat_shamir_rng_phantom: PhantomData<FSG>,
    _endo_mul_curve: PhantomData<G>,
    _endo_mul_curve_gadget: PhantomData<GG>,
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF>
            + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>,
    > PolynomialCommitmentVerifierGadget<ConstraintF, G, InnerProductArgPC<G, FS>>
    for InnerProductArgGadget<ConstraintF, FSG, G, GG>
{
    type VerifierKey = IPAVerifierKeyGadget<ConstraintF, G, GG>;
    type VerifierState = IPAVerifierState<ConstraintF, G, GG>;
    type Commitment = GG;
    type Proof = IPAProofGadget<ConstraintF, G, GG, FS, FSG>;
    type MultiPointProof = IPAMultiPointProof<ConstraintF, G, GG, FS, FSG>;
    type RandomOracle = FSG;
    type Error = Error;

    fn mul_by_challenge<'a, CS: ConstraintSystemAbstract<ConstraintF>,
        IT: Iterator<Item = &'a Boolean>>(cs: CS, base: &Self::Commitment, challenge: IT) -> Result<Self::Commitment, SynthesisError> {
        safe_mul::<ConstraintF, G, GG, _, _>(cs, base, challenge, true)
    }

    fn challenge_to_non_native_field_element<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, challenge: &[Boolean]) -> Result<NonNativeFieldGadget<G::ScalarField, ConstraintF>, SynthesisError> {
        let mut challenge_for_endo_mul =
            GG::endo_rep_to_scalar_bits(cs.ns(|| "apply endomorphism"), challenge.to_vec())?;
        // endo_rep_to_scalar_bits returns a little-endian bit representation, we need a big-endian
        // one to correctly instantiate a non-native field gadget
        challenge_for_endo_mul.reverse();
        NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(
            cs.ns(|| "convert lambda to non native field gadget"),
            &challenge_for_endo_mul,
        )
    }

    fn succinct_verify<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &Self::VerifierKey,
        commitment: &Self::Commitment,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        value: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        proof: &Self::Proof,
        random_oracle: &mut Self::RandomOracle,
    ) -> Result<Self::VerifierState, Self::Error> {
        if proof.vec_l.len() != proof.vec_r.len() {
            Err(SynthesisError::Other(String::from(format!("vec_l and vec_r in proof do not have the same length: len(vec_l)={}, len(vec_r)={}", proof.vec_l.len(), proof.vec_r.len()))))?;
        }

        if proof.hiding_comm.is_some() != proof.rand.is_some() {
            Err(SynthesisError::Other(String::from("hiding commitment and hiding randomness must be either both present or both missing")))?;
        }

        let mut non_hiding_commitment = commitment.clone();

        if let Some(comm) = &proof.hiding_comm {
            random_oracle.enforce_absorb(cs.ns(|| "absorb hiding commitment"), comm.clone())?;
            let hiding_challenge = random_oracle
                .enforce_squeeze_128_bits_challenges(cs.ns(|| "squeeze hiding challenge"), 1)?[0];
            let hiding_randomness_bits = proof.rand.as_ref().unwrap();
            //ToDo: conversion to NonNativeFieldGadget is necessary only because hiding_randomness
            // must be absorbed to be compliant with the primitive. Since this absorb may seem
            // unnecessary, we may remove it also from here once it is removed in the primitive
            let hiding_randomness=
                NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(cs.ns(|| "hiding randomness to bits"), &hiding_randomness_bits)?;
            random_oracle.enforce_absorb(
                cs.ns(|| "absorb hiding randomness"),
                &[hiding_randomness][..],
            )?;

            let comm_times_challenge =
                safe_mul::<ConstraintF, G, GG, _, _>(
                    cs.ns(|| "hiding_commitment * hiding_challenge"),
                    &comm,
                    hiding_challenge.iter(),
                    true,
                )?;
            let rand_times_s = vk.s.mul_bits(
                cs.ns(|| "vk.s * hiding_randomness"),
                hiding_randomness_bits.iter().rev(),
            )?; // reverse order of bits since mul_bits requires little endian representation
            non_hiding_commitment = non_hiding_commitment.add(
                cs.ns(|| "add hiding_commitment*hiding_challenge to original commitment"),
                &comm_times_challenge,
            )?;
            non_hiding_commitment = non_hiding_commitment.sub(
                cs.ns(|| "sub vk.s*hiding_randomness to commitment"),
                &rand_times_s,
            )?;
        }

        let round_challenge = random_oracle
            .enforce_squeeze_128_bits_challenges(cs.ns(|| "squeeze round-0 challenge"), 1)?[0];

        let mut round_challenges = Vec::with_capacity(proof.vec_l.len());

        let h_prime =
            vk.h.endo_mul(cs.ns(|| "h' = vk.h*round_challenge"), &round_challenge)?;
        let value_bits = value.to_bits(cs.ns(|| "value to bits"))?;
        let value_times_h_prime =
            h_prime.mul_bits(cs.ns(|| "value*h'"), value_bits.iter().rev())?;
        non_hiding_commitment = non_hiding_commitment
            .add(cs.ns(|| "add value*h' to commitment"), &value_times_h_prime)?;
        for (i, (el_vec_l, el_vec_r)) in proof.vec_l.iter().zip(proof.vec_r.iter()).enumerate() {
            random_oracle.enforce_absorb(
                cs.ns(|| format!("absorb commitments for round {}", i + 1)),
                [el_vec_l.clone(), el_vec_r.clone()],
            )?;
            let round_challenge = random_oracle.enforce_squeeze_128_bits_challenges(
                cs.ns(|| format!("squeeze round-{} challenge", i + 1)),
                1,
            )?[0];
            // compute round_challenge*el_vec_r dealing with the case el_vec_r is zero
            let challenge_times_r =
                safe_mul::<ConstraintF, G, GG, _, _>(
                    cs.ns(|| format!("round_challenge_{}*vec_r_{}", i + 1, i)),
                    el_vec_r,
                    round_challenge.iter(),
                    true,
                )?;
            non_hiding_commitment = non_hiding_commitment.add(
                cs.ns(|| format!("add round_challenge_{}*vec_r_{} to commitment", i + 1, i)),
                &challenge_times_r,
            )?;
            //apply endomorphism to round_challenge, as challenge_times_r = r*endomorphism(round_challenge),
            // since endo_mul is employed for the multiplication. Therefore,
            // the actual challenge to be employed for the bullet polynomial and to be inverted to
            // be multiplied to l is endomorphism(round_challenge)
            let round_challenge_endo = GG::endo_rep_to_scalar_bits(
                cs.ns(|| format!("apply endomorphism to round_challenge_{}", i + 1)),
                round_challenge.to_vec(),
            )?;
            let round_challenge_be_bits = round_challenge_endo
                .iter()
                .rev()
                .cloned()
                .collect::<Vec<_>>();
            let round_challenge_in_scalar_field =
                NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(
                    cs.ns(|| {
                        format!(
                            "converting round_challenge_{} to scalar field element",
                            i + 1
                        )
                    }),
                    &round_challenge_be_bits,
                )?;
            let round_challenge_inverse = round_challenge_in_scalar_field
                .inverse(cs.ns(|| format!("invert round_challenge_{}", i + 1)))?;
            let round_challenge_inverse_bits = round_challenge_inverse
                .to_bits_for_normal_form(cs.ns(|| format!("convert round_challenge_{} inverse to bits", i + 1)))?;
            // compute round_challenge^{-1}*el_vec_l dealing with the case el_vec_l is zero
            let challenge_inv_times_l =
                safe_mul::<ConstraintF, G, GG, _, _>(
                    cs.ns(|| format!("round_challenge_inverse_{}*vec_l_{}", i + 1, i)),
                    el_vec_l,
                    round_challenge_inverse_bits.iter().rev(),
                    false,
                )?;
            non_hiding_commitment = non_hiding_commitment.add(
                cs.ns(|| {
                    format!(
                        "add round_challenge_inverse_{}*vec_l_{} to commitment",
                        i + 1,
                        i
                    )
                }),
                &challenge_inv_times_l,
            )?;
            round_challenges.push(round_challenge_in_scalar_field);
        }
        // evaluate bullet polynomial h over point
        let mut point_power = point.clone();
        let one = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::one(
            cs.ns(|| "alloc 1 in scalar field"),
        )?;
        let mut bullet_polynomial_evaluation = one.clone();

        for (i, round_challenge) in round_challenges.iter().rev().enumerate() {
            let challenge_times_point_power = point_power.mul_without_prereduce(
                cs.ns(|| {
                    format!(
                        "round_challenge_{}*point^(2^{})",
                        round_challenges.len() - i,
                        i
                    )
                }),
                &round_challenge,
            )?;
            let current_term = challenge_times_point_power.add_constant(
                cs.ns(|| {
                    format!(
                        "round_challenge_{}*point^(2^{})+1",
                        round_challenges.len() - i,
                        i
                    )
                }),
                &G::ScalarField::one(),
            )?;
            let current_term = current_term.reduce(cs.ns(|| {
                format!(
                    "reduce round_challenge_{}*point^(2^{})+1",
                    round_challenges.len() - i,
                    i
                )
            }))?;

            if i != 0 {
                bullet_polynomial_evaluation.mul_in_place(
                    cs.ns(|| {
                        format!(
                            "update bullet polynomial with challenge {}",
                            round_challenges.len() - i
                        )
                    }),
                    &current_term,
                )?;
            } else {
                // avoid costly multiplication in the first iteration
                bullet_polynomial_evaluation = current_term;
            }

            if i == round_challenges.len() - 1 {
                //avoid costly squaring in the last iteration
                continue;
            }

            point_power.square_in_place(cs.ns(|| format!("compute point^(2^{})", i)))?;
        }

        let c = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(cs.ns(|| "proof.c from bits"), &proof.c)?;
        let v_prime =c.mul(cs.ns(|| "v'=c*h(point)"), &bullet_polynomial_evaluation)?;
        let c_times_final_comm_key =
            safe_mul::<ConstraintF, G, GG, _, _>(
                cs.ns(|| "c*g_final"),
                &proof.final_comm_key,
                proof.c.iter().rev(),
                false,
            )?;
        let v_prime_bits = v_prime.to_bits_for_normal_form(cs.ns(|| "v' to bits"))?;
        let v_prime_times_h_prime =
            h_prime.mul_bits(cs.ns(|| "v'*h'"), v_prime_bits.iter().rev())?;

        let final_commitment = c_times_final_comm_key
            .add(cs.ns(|| "compute final commitment"), &v_prime_times_h_prime)?;

        final_commitment.enforce_equal(
            cs.ns(|| "check that final_commitment == non_hiding_commitment"),
            &non_hiding_commitment,
        )?;

        Ok(IPAVerifierState::new(
            BulletPolynomial::new(round_challenges),
            final_commitment,
        ))
    }

    /*/// succinct check of the verification of an opening proof for multiple polynomials in the
    /// same point
    fn succinct_verify_single_point_multi_poly<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &Self::VerifierKey,
        labeled_commitments: &[LabeledCommitmentGadget<Self, ConstraintF, G, PC>], //ToDo: see if we can take an impl IntoIterator as for the primitive
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        values: &[NonNativeFieldGadget<G::ScalarField, ConstraintF>],
        proof: &Self::Proof,
        random_oracle: &mut Self::RandomOracle,
    ) -> Result<Self::VerifierState, Self::Error> {
        let lambda = random_oracle.enforce_squeeze_128_bits_challenges(
            cs.ns(|| "squeeze lambda for single-point-multi-poly verify"),
            1,
        )?[0];
        // lambda is multiplied to batched_commitment with endo_mul, which implicitly applies an
        // endomorphism to lambda before multiplication. `lambda_for_endo_mul` is the result of
        // applying such endomorphism to lambda, which is needed as batched_value is not multiplied
        // with endo_mul to lambda
        let mut lambda_for_endo_mul =
            GG::endo_rep_to_scalar_bits(cs.ns(|| "apply endomorphism to lambda"), lambda.to_vec())?;
        // endo_rep_to_scalar_bits returns a little-endian bit representation, we need a big-endian
        // one to correctly instantiate a non-native field gadget
        lambda_for_endo_mul.reverse();
        let lambda_non_native = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(
            cs.ns(|| "convert lambda to non native field gadget"),
            &lambda_for_endo_mul,
        )?;
        let default_commitment = LabeledCommitmentGadget::new(
            String::from("default commitment"),
            Self::Commitment::zero(&mut cs)?,
        );
        let mut commitments_iter = labeled_commitments.iter().rev();
        let mut batched_commitment = commitments_iter
            .next()
            .unwrap_or(&default_commitment)
            .commitment()
            .clone();

        let zero_value = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::zero(&mut cs)?;
        let mut values_iter = values.iter().rev();
        let mut batched_value = values_iter.next().unwrap_or(&zero_value).clone();

        for (i, (commitment, value)) in commitments_iter.zip(values_iter).enumerate() {
            batched_commitment = safe_mul::<ConstraintF, G, GG, PC, Self, _, _>(
                cs.ns(|| format!("lambda*batched_commitment_{}", i)),
                &batched_commitment,
                lambda.iter(),
                true,
            )?;
            // batched_commitment = batched_commitment.endo_mul(cs.ns(|| format!("lambda*batched_commitment_{}", i)), &lambda)?;
            batched_commitment = batched_commitment.add(
                cs.ns(|| format!("add commitment {} to batched_commitment", i)),
                commitment.commitment(),
            )?;

            let batched_value_times_lambda = batched_value.mul_without_prereduce(
                cs.ns(|| format!("lambda*batched_value_{}", i)),
                &lambda_non_native,
            )?;
            let value = FromGadget::from(value, cs.ns(|| format!("value {} to mul result", i)))?;
            batched_value =
                batched_value_times_lambda.add(cs.ns(|| format!("add value {} to batched_value", i)), &value)?.reduce(cs.ns(|| format!("reduce batched_value_{}", i)))?;
        }

        Self::succinct_verify(
            &mut cs,
            &vk,
            &batched_commitment,
            point,
            &batched_value,
            &proof,
            random_oracle,
        )
    }

    /// succinct check of the verification of an opening proof for multiple polynomials in
    /// multiple points
    fn succinct_verify_multi_poly_multi_point<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &Self::VerifierKey,
        labeled_commitments: &[LabeledCommitmentGadget<Self, ConstraintF, G, PC>],
        points: &QueryMap<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        values: &Evaluations<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        proof: &Self::MultiPointProof,
        random_oracle: &mut Self::RandomOracle,
    ) -> Result<Self::VerifierState, Self::Error> {
        let commitment_map: BTreeMap<_, _> = labeled_commitments
            .into_iter()
            .map(|commitment| (commitment.label(), commitment.commitment()))
            .collect();

        let lambda_bits = random_oracle.enforce_squeeze_128_bits_challenges(
            cs.ns(|| "squeezing random challenge for multi-point-multi-poly verify"),
            1,
        )?[0];

        // need to apply endo mul endomorphism to lambda, as the random oracle in the opening proof already applies the endomorphism to the squeezed bits
        let mut lambda_endo_bits = GG::endo_rep_to_scalar_bits(
            cs.ns(|| "apply endomorphism to lambda"),
            lambda_bits.to_vec(),
        )?;
        // endo_rep_to_scalar_bits returns a little-endian bit representation, we need a big-endian
        // one to correctly instantiate a non-native field gadget
        lambda_endo_bits.reverse();
        let lambda = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(
            cs.ns(|| "convert lambda to non native field gadget"),
            &lambda_endo_bits,
        )?;

        random_oracle.enforce_absorb(
            cs.ns(|| "absorb commitment to polynomial h"),
            proof.get_h_commitment().clone(),
        )?;
        let evaluation_point_bits = random_oracle.enforce_squeeze_128_bits_challenges(
            cs.ns(|| "squeeze evaluation point for multi-point multi-poly verify"),
            1,
        )?[0];
        // need to apply endo mul endomorphism to evaluation point, as the random oracle in the opening proof already applies the endomorphism to the squeezed bits
        let mut evaluation_point_endo_bits = GG::endo_rep_to_scalar_bits(
            cs.ns(|| "apply endomorphism to evaluation point"),
            evaluation_point_bits.to_vec(),
        )?;
        // endo_rep_to_scalar_bits returns a little-endian bit representation, we need a big-endian
        // one to correctly instantiate a non-native field gadget
        evaluation_point_endo_bits.reverse();
        let evaluation_point = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(
            cs.ns(|| "evaluation point from squeezed bits"),
            &evaluation_point_endo_bits,
        )?;

        let mut points_iter = points.iter().rev();
        let zero_value = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::zero(&mut cs)?;
        let default_label = (String::from("default label"), String::from("default label"));
        let ((label, point_label), point) =
            points_iter.next().unwrap_or((&default_label, &zero_value));
        let commitment = *commitment_map
            .get(label)
            .ok_or(SynthesisError::Other(String::from(format!(
                "commitment with label {} not found",
                label
            ))))?;
        let value =
            values
                .get(&(label.clone(), point_label.clone()))
                .ok_or(SynthesisError::Other(String::from(format!(
                    "evaluation for point {} not found",
                    point_label
                ))))?;
        let z_i_over_z_value = evaluation_point
            .sub(cs.ns(|| "evaluation_point - point for last point"), &point)?
            .inverse(cs.ns(|| "(evaluation_point - point)^-1 for last point"))?;
        let z_i_over_z_bits =
            z_i_over_z_value.to_bits_for_normal_form(cs.ns(|| "z_i_over_z_value to bits for last point"))?;

        let mut batched_commitment = safe_mul::<ConstraintF, G, GG, PC, Self, _, _>(
            cs.ns(|| "commitment*z_i_over_z for last point"),
            &commitment,
            z_i_over_z_bits.iter().rev(),
            false,
        )?; // reverse order of bits since mul_bits requires little endian representation
        let mut batched_value = value.mul(
            cs.ns(|| "value*z_i_over_z for last point"),
            &z_i_over_z_value,
        )?;

        for ((label, point_label), point) in points_iter {
            let combined_label = format!("{}:{}", label, point_label); // unique label across all iterations obtained by combining label and point_label
            let commitment =
                *commitment_map
                    .get(label)
                    .ok_or(SynthesisError::Other(String::from(format!(
                        "commitment with label {} not found",
                        label
                    ))))?;
            let value =
                values
                    .get(&(label.clone(), point_label.clone()))
                    .ok_or(SynthesisError::Other(String::from(format!(
                        "evaluation for point {} not found",
                        point_label
                    ))))?;
            // check that evaluation point is different than the current point, as we later need
            // to compute the inverse of `evaluation_point - point`
            // ToDo: can probably be removed as inverse will fail if evaluation_point and point are equal
            evaluation_point.enforce_not_equal(
                cs.ns(|| {
                    format!(
                        "enforce evaluation_point != point with label {}",
                        combined_label
                    )
                }),
                &point,
            )?;

            let z_i_over_z_value = evaluation_point
                .sub(
                    cs.ns(|| format!("evaluation_point - point with label {}", combined_label)),
                    &point,
                )?
                .inverse(cs.ns(|| {
                    format!(
                        "(evaluation_point - point with label {})^-1",
                        combined_label
                    )
                }))?;
            let z_i_over_z_bits = z_i_over_z_value
                .to_bits_for_normal_form(cs.ns(|| format!("z_i_over_z to bits for label {}", combined_label)))?;
            let to_be_added_commitment = safe_mul::<ConstraintF, G, GG, PC, Self, _, _>(
                cs.ns(|| format!("commitment*z_i_over_z for label {}", combined_label)),
                &commitment,
                z_i_over_z_bits.iter().rev(), // must be reversed as safe_mul wants bits in little-endian
                false,
            )?;
            let to_be_added_value = value.mul_without_prereduce(
                cs.ns(|| format!("value*z_i_over_z for label {}", combined_label)),
                &z_i_over_z_value,
            )?;

            batched_commitment = safe_mul::<ConstraintF, G, GG, PC, Self, _, _>(
                cs.ns(|| format!("batched_commitment*lambda for label {}", combined_label)),
                &batched_commitment,
                lambda_bits.iter(),
                true,
            )?;
            batched_commitment = batched_commitment.add(
                cs.ns(|| format!("add commitment for label {}", combined_label)),
                &to_be_added_commitment,
            )?;

            let batched_value_times_lambda = batched_value.mul_without_prereduce(
                cs.ns(|| format!("batched_value*lambda for label {}", combined_label)),
                &lambda,
            )?;
            batched_value = batched_value_times_lambda.add(
                cs.ns(|| format!("add value for point for label {}", combined_label)),
                &to_be_added_value,
            )?.reduce(cs.ns(|| format!("reduce batched value for label {}", combined_label)))?;
        }
        batched_commitment =
            batched_commitment.sub(cs.ns(|| "sub h commitment"), &proof.get_h_commitment())?;
        Self::succinct_verify(
            cs.ns(|| "succinct verify on batched"),
            &vk,
            &batched_commitment,
            &evaluation_point,
            &batched_value,
            &proof.get_proof(),
            random_oracle,
        )
    }*/
}
