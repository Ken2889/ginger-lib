use crate::ipa_pc::constraints::data_structures::{
    IPAMultiPointProofGadget, IPAProofGadget, IPAVerifierKeyGadget, IPAVerifierStateGadget,
    SuccinctCheckPolynomialGadget,
};
use crate::ipa_pc::InnerProductArgPC;
use crate::{safe_mul_bits, Error, PolynomialCommitmentVerifierGadget};
use algebra::{EndoMulCurve, PrimeField};
use fiat_shamir::constraints::FiatShamirRngGadget;
use fiat_shamir::FiatShamirRng;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::boolean::Boolean;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::groups::EndoMulCurveGadget;
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use r1cs_std::FromBitsGadget;
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::marker::PhantomData;

mod data_structures;

#[cfg(feature = "circuit-friendly")]
#[cfg(test)]
mod tests;

/// poly-commit verifier gadget implementation from the inner-product argument ([BCMS20](https://eprint.iacr.org/2020/499))
pub struct InnerProductArgGadget<
    ConstraintF: PrimeField,
    FSG: FiatShamirRngGadget<ConstraintF>,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: 'static
        + EndoMulCurveGadget<G, ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
> {
    _constraint_field_phantom: PhantomData<ConstraintF>,
    _fiat_shamir_rng_phantom: PhantomData<FSG>,
    _endo_mul_curve: PhantomData<G>,
    _endo_mul_curve_gadget: PhantomData<GG>,
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: 'static
            + EndoMulCurveGadget<G, ConstraintF>
            + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>,
    > PolynomialCommitmentVerifierGadget<ConstraintF, G, InnerProductArgPC<G, FS>>
    for InnerProductArgGadget<ConstraintF, FSG, G, GG>
{
    type VerifierKeyGadget = IPAVerifierKeyGadget<ConstraintF, G, GG>;
    type VerifierStateGadget = IPAVerifierStateGadget<ConstraintF, G, GG>;
    type CommitmentGadget = GG;
    type ProofGadget = IPAProofGadget<ConstraintF, G, GG, FS, FSG>;
    type MultiPointProofGadget = IPAMultiPointProofGadget<ConstraintF, G, GG, FS, FSG>;
    type RandomOracleGadget = FSG;
    type Error = Error;

    fn mul_by_challenge<
        'a,
        CS: ConstraintSystemAbstract<ConstraintF>,
        IT: Iterator<Item = &'a Boolean>,
    >(
        mut cs: CS,
        base_point: &Self::CommitmentGadget,
        challenge: IT,
    ) -> Result<Self::CommitmentGadget, SynthesisError> {
        // we need to employ a rng with fixed seed in order to deterministically generated a
        // non zero base element in PC::Commitment
        let rng = &mut XorShiftRng::seed_from_u64(42);
        let mut non_trivial_base_constant = G::rand(rng);
        while non_trivial_base_constant.is_zero() {
            non_trivial_base_constant = G::rand(rng);
        }
        let non_trivial_base_gadget = Self::CommitmentGadget::from_value(
            cs.ns(|| "alloc non trivial base constant"),
            &non_trivial_base_constant,
        );
        let zero = Self::CommitmentGadget::zero(cs.ns(|| "alloc constant 0"))?;

        let is_zero = base_point.is_zero(cs.ns(|| "check if base point is zero"))?;
        let non_trivial_base_point = Self::CommitmentGadget::conditionally_select(
            cs.ns(|| "select non trivial base point for mul"),
            &is_zero,
            &non_trivial_base_gadget,
            &base_point,
        )?;
        let safe_mul_res = non_trivial_base_point.endo_mul(
            cs.ns(|| "base_point*scalar"),
            challenge.cloned().collect::<Vec<_>>().as_slice(),
        )?;
        Self::CommitmentGadget::conditionally_select(
            cs.ns(|| "select correct result for safe mul"),
            &is_zero,
            &zero,
            &safe_mul_res,
        )
    }

    fn challenge_to_non_native_field_element<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        challenge: &[Boolean],
    ) -> Result<NonNativeFieldGadget<G::ScalarField, ConstraintF>, SynthesisError> {
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
        vk: &Self::VerifierKeyGadget,
        commitment: &Self::CommitmentGadget,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        value: &Vec<Boolean>,
        proof: &Self::ProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error> {
        if proof.vec_l.len() != proof.vec_r.len() {
            Err(SynthesisError::Other(String::from(format!("vec_l and vec_r in proof do not have the same length: len(vec_l)={}, len(vec_r)={}", proof.vec_l.len(), proof.vec_r.len()))))?;
        }

        if proof.hiding_comm.is_some() != proof.rand.is_some() {
            Err(SynthesisError::Other(String::from("hiding commitment and hiding randomness must be either both present or both missing")))?;
        }

        let mut non_hiding_commitment = commitment.clone();

        if let Some(comm) = &proof.hiding_comm {
            random_oracle.enforce_record(cs.ns(|| "absorb hiding commitment"), comm.clone())?;
            let hiding_challenge = random_oracle
                .enforce_get_challenge::<_, 128>(cs.ns(|| "squeeze hiding challenge"))?;
            let hiding_randomness_bits = proof.rand.as_ref().unwrap();
            random_oracle.enforce_record(
                cs.ns(|| "absorb hiding randomness"),
                hiding_randomness_bits.as_slice(),
            )?;

            let comm_times_challenge = comm.endo_mul(
                cs.ns(|| "hiding_commitment * hiding_challenge"),
                &hiding_challenge,
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

        let round_challenge =
            random_oracle.enforce_get_challenge::<_, 128>(cs.ns(|| "squeeze round-0 challenge"))?;

        let mut round_challenges = Vec::with_capacity(proof.vec_l.len());

        let h_prime =
            vk.h.endo_mul(cs.ns(|| "h' = vk.h*round_challenge"), &round_challenge)?;
        let value_times_h_prime = h_prime.mul_bits(cs.ns(|| "value*h'"), value.iter().rev())?;
        non_hiding_commitment = non_hiding_commitment
            .add(cs.ns(|| "add value*h' to commitment"), &value_times_h_prime)?;
        for (i, (el_vec_l, el_vec_r)) in proof.vec_l.iter().zip(proof.vec_r.iter()).enumerate() {
            random_oracle.enforce_record(
                cs.ns(|| format!("absorb commitments for round {}", i + 1)),
                [el_vec_l.clone(), el_vec_r.clone()],
            )?;
            let round_challenge = random_oracle.enforce_get_challenge::<_, 128>(
                cs.ns(|| format!("squeeze round-{} challenge", i + 1)),
            )?;
            // compute round_challenge*el_vec_r dealing with the case el_vec_r is zero
            let challenge_times_r = <Self as PolynomialCommitmentVerifierGadget<
                ConstraintF,
                G,
                InnerProductArgPC<G, FS>,
            >>::mul_by_challenge(
                cs.ns(|| format!("round_challenge_{}*vec_r_{}", i + 1, i)),
                el_vec_r,
                round_challenge.iter(),
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
            let round_challenge_inverse_bits = round_challenge_inverse.to_bits_for_normal_form(
                cs.ns(|| format!("convert round_challenge_{} inverse to bits", i + 1)),
            )?;
            // compute round_challenge^{-1}*el_vec_l dealing with the case el_vec_l is zero
            let challenge_inv_times_l =
                safe_mul_bits::<ConstraintF, G, InnerProductArgPC<G, FS>, Self, _, _>(
                    cs.ns(|| format!("round_challenge_inverse_{}*vec_l_{}", i + 1, i)),
                    el_vec_l,
                    round_challenge_inverse_bits.iter().rev(),
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
        let bullet_polynomial = SuccinctCheckPolynomialGadget::new(round_challenges);
        let bullet_polynomial_evaluation =
            bullet_polynomial.evaluate(cs.ns(|| "evaluate bullet polynomial"), point)?;

        let c = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(
            cs.ns(|| "proof.c from bits"),
            &proof.c,
        )?;
        let v_prime = c.mul(cs.ns(|| "v'=c*h(point)"), &bullet_polynomial_evaluation)?;
        let c_times_final_comm_key =
            safe_mul_bits::<ConstraintF, G, InnerProductArgPC<G, FS>, Self, _, _>(
                cs.ns(|| "c*g_final"),
                &proof.final_comm_key,
                proof.c.iter().rev(),
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

        Ok(IPAVerifierStateGadget::new(
            bullet_polynomial,
            final_commitment,
        ))
    }
}
