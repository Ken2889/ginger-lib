use crate::ipa_pc::constraints::data_structures::{
    BulletPolynomial, IPAMultiPointProof, IPAProofGadget, IPAVerifierKeyGadget, IPAVerifierState,
};
use crate::ipa_pc::InnerProductArgPC;
use crate::{safe_mul, Error, PolynomialCommitmentVerifierGadget};
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

mod data_structures;

#[cfg(feature = "circuit-friendly")]
#[cfg(test)]
mod tests;

/// poly-commit verifier gadget implementation from the inner-product argument ([BCMS20](https://eprint.iacr.org/2020/499))
pub struct InnerProductArgGadget<ConstraintF: PrimeField, FSG: FiatShamirRngGadget<ConstraintF>> {
    _constraint_field_phantom: PhantomData<ConstraintF>,
    _fiat_shamir_rng_phantom: PhantomData<FSG>,
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF>
            + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>,
    > PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, InnerProductArgPC<G, FS>>
    for InnerProductArgGadget<ConstraintF, FSG>
{
    type VerifierKey = IPAVerifierKeyGadget<ConstraintF, G, GG>;
    type VerifierState = IPAVerifierState<ConstraintF, G, GG>;
    type Commitment = GG;
    type Proof = IPAProofGadget<ConstraintF, G, GG, FS, FSG>;
    type MultiPointProof = IPAMultiPointProof<ConstraintF, G, GG, FS, FSG>;
    type RandomOracle = FSG;
    type Error = Error;

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
                safe_mul::<ConstraintF, G, GG, InnerProductArgPC<G, FS>, Self, _, _>(
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
                safe_mul::<ConstraintF, G, GG, InnerProductArgPC<G, FS>, Self, _, _>(
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
                safe_mul::<ConstraintF, G, GG, InnerProductArgPC<G, FS>, Self, _, _>(
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
            safe_mul::<ConstraintF, G, GG, InnerProductArgPC<G, FS>, Self, _, _>(
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
}
