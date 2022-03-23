use crate::{Error as PolyError, Evaluations, PolynomialCommitment, QueryMap};
use algebra::{Group, PrimeField, UniformRand};
use fiat_shamir::constraints::FiatShamirRngGadget;
use num_traits::Zero;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::fields::{nonnative::nonnative_field_gadget::NonNativeFieldGadget, FieldGadget};
use r1cs_std::groups::GroupGadget;
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use r1cs_std::{alloc::AllocGadget, FromBitsGadget};
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::collections::BTreeMap;

pub mod data_structures;
pub use data_structures::*;

#[cfg(test)]
#[cfg(feature = "circuit-friendly")]
pub mod tests;
use r1cs_std::boolean::Boolean;
use r1cs_std::eq::EqGadget;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::prelude::{CondSelectGadget, ConstantGadget};
use r1cs_std::FromGadget;

/// multiply `base_point` to `scalar` dealing with the corner case that `base_point` may be zero
/// `scalar` must be an iterator over the bits of the scalar in *little-endian* order
pub(crate) fn safe_mul_bits<'a, ConstraintF, G, PC, PCG, CS, IT>(
    mut cs: CS,
    base_point: &PCG::CommitmentGadget,
    scalar: IT,
) -> Result<PCG::CommitmentGadget, SynthesisError>
where
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
    CS: ConstraintSystemAbstract<ConstraintF>,
    IT: Iterator<Item = &'a Boolean>,
{
    /*
    We deterministically sample a non zero commitment C' and then we perform the following steps:
    - let `non_trivial_base_point` = cond_select(is_zero, C', base_point), where `is_zero` is true
    iff `base_point` is zero. This ensures that `non_trivial_base_point` will always be a non-zero
    commitment, which can then be safely multiplied by `scalar`
    - the result is then computed as cond_select(is_zero, 0, non_trivial_base_point*scalar); thus,
    if `base_point` is zero, then the result is 0 and the product `non_trivial_base_point`*`scalar`
    is discarded, otherwise the result will just be `base_point`*`scalar`
    */
    // we need to employ a rng with fixed seed in order to deterministically generated a
    // non zero base element in PC::Commitment
    let rng = &mut XorShiftRng::seed_from_u64(42);
    let mut non_trivial_base_constant = PC::Commitment::rand(rng);
    while non_trivial_base_constant.is_zero() {
        non_trivial_base_constant = PC::Commitment::rand(rng);
    }
    let non_trivial_base_gadget = PCG::CommitmentGadget::from_value(
        cs.ns(|| "alloc non trivial base constant"),
        &non_trivial_base_constant,
    );
    let zero = PCG::CommitmentGadget::zero(cs.ns(|| "alloc constant 0"))?;

    let is_zero = base_point.is_zero(cs.ns(|| "check if base point is zero"))?;
    let non_trivial_base_point = PCG::CommitmentGadget::conditionally_select(
        cs.ns(|| "select non trivial base point for mul"),
        &is_zero,
        &non_trivial_base_gadget,
        &base_point,
    )?;
    let safe_mul_res = non_trivial_base_point.mul_bits(cs.ns(|| "base_point*scalar"), scalar)?;
    PCG::CommitmentGadget::conditionally_select(
        cs.ns(|| "select correct result for safe mul"),
        &is_zero,
        &zero,
        &safe_mul_res,
    )
}

/// Helper function employed by implementations of `succinct_verify_multi_poly_multi_point` that,
/// given as inputs the commitments and the evaluations of the polynomials for
/// a `multi_point` succinct verification, batches the commitments and the evaluation in a single
/// commitment and in a single value, respectively.
pub(crate) fn multi_poly_multi_point_batching<
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
    CS: ConstraintSystemAbstract<ConstraintF>,
>(
    mut cs: CS,
    labeled_commitments: &[LabeledCommitmentGadget<PCG, ConstraintF, G, PC>],
    points: &QueryMap<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
    values: &Evaluations<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
    evaluation_point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
    lambda_bits: &[Boolean],
) -> Result<
    (
        PCG::CommitmentGadget,
        NonNativeFieldGadget<G::ScalarField, ConstraintF>,
    ),
    PCG::Error,
> {
    let commitment_map: BTreeMap<_, _> = labeled_commitments
        .into_iter()
        .map(|commitment| (commitment.label(), commitment.commitment()))
        .collect();

    let lambda = PCG::challenge_to_non_native_field_element(
        cs.ns(|| "convert lambda to non native field gadget"),
        &lambda_bits,
    )?;
    /*
    Given a set of points x_1, ..., x_n and an evaluation point x distinct from all the other
    points, we need to batch the commitments C_1, ..., C_n in a single commitment
    C=C_1*(x-x_1)^-1+lambda*C_2*(x-x_2)^-1+lambda^2*C_3*(x-x_3)^-1 + ... + lambda^(n-1)*C_n*(x-x_n)^-1.
    To do this, we again use Horner scheme:
    - Initialize C = C_n*(x-x_n)^-1
    - For each point x_i, where i varies from n-1 to 1, we update C = C_i*(x-x_i)^-1 + lambda*C
    Therefore, we iterate over the set of points in reverse order, fetching the corresponding
    commitment from `commitment_map`. The same strategy is applied to batch values
    */

    // here we fetch the point x_n to initialize both the batched commitment and the batched

    // batched_commitment and batched_value are initialized to None as in the first iteration
    // we need to proper initialize them for the Horner scheme
    let mut batched_commitment = None;
    let mut batched_value = None;

    for (point_label, (point, poly_labels)) in points.iter().rev() {
        // check that evaluation point is different than the current point, as we later need
        // to compute the inverse of `evaluation_point - point`
        //ToDo: can probably be removed as inverse will fail if evaluation_point and point are equal,
        // to be confirmed in review
        evaluation_point.enforce_not_equal(
            cs.ns(|| {
                format!(
                    "enforce evaluation_point != point with label {}",
                    point_label
                )
            }),
            &point,
        )?;

        let z_i_over_z_value = evaluation_point
            .sub(
                cs.ns(|| format!("evaluation_point - point with label {}", point_label)),
                &point,
            )?
            .inverse(
                cs.ns(|| format!("(evaluation_point - point with label {})^-1", point_label)),
            )?;
        let z_i_over_z_bits = z_i_over_z_value.to_bits_for_normal_form(
            cs.ns(|| format!("z_i_over_z to bits for label {}", point_label)),
        )?;
        for label in poly_labels.iter().rev() {
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
                        "evaluation for label {} not found",
                        combined_label
                    ))))?;
            match (batched_commitment, batched_value) {
                (None, None) => {
                    batched_commitment = Some(safe_mul_bits::<ConstraintF, G, PC, PCG, _, _>(
                        cs.ns(|| "commitment*z_i_over_z for last point"),
                        &commitment,
                        z_i_over_z_bits.iter().rev(),
                    )?); // reverse order of bits since mul_bits requires little endian representation
                    batched_value = Some(value.mul(
                        cs.ns(|| "value*z_i_over_z for last point"),
                        &z_i_over_z_value,
                    )?);
                }
                (Some(comm), Some(val)) => {
                    let to_be_added_commitment = safe_mul_bits::<ConstraintF, G, PC, PCG, _, _>(
                        cs.ns(|| format!("commitment*z_i_over_z for label {}", combined_label)),
                        &commitment,
                        z_i_over_z_bits.iter().rev(), // must be reversed as mul_bits wants bits in little-endian
                    )?;
                    let to_be_added_value = value.mul_without_prereduce(
                        cs.ns(|| format!("value*z_i_over_z for label {}", combined_label)),
                        &z_i_over_z_value,
                    )?;

                    let batched_commitment_times_lambda = PCG::mul_by_challenge(
                        cs.ns(|| format!("batched_commitment*lambda for label {}", combined_label)),
                        &comm,
                        lambda_bits.iter(),
                    )?;
                    batched_commitment = Some(batched_commitment_times_lambda.add(
                        cs.ns(|| format!("add commitment for label {}", combined_label)),
                        &to_be_added_commitment,
                    )?);

                    let batched_value_times_lambda = val.mul_without_prereduce(
                        cs.ns(|| format!("batched_value*lambda for label {}", combined_label)),
                        &lambda,
                    )?;
                    batched_value = Some(
                        batched_value_times_lambda
                            .add(
                                cs.ns(|| {
                                    format!("add value for point for label {}", combined_label)
                                }),
                                &to_be_added_value,
                            )?
                            .reduce(cs.ns(|| {
                                format!("reduce batched value for label {}", combined_label)
                            }))?,
                    );
                }
                _ => unreachable!(),
            }
        }
    }
    if batched_commitment.is_none() || batched_value.is_none() {
        Err(SynthesisError::Other(
            "no evaluation points provided".to_string(),
        ))?
    }

    Ok((batched_commitment.unwrap(), batched_value.unwrap()))
}

impl From<SynthesisError> for PolyError {
    fn from(err: SynthesisError) -> Self {
        Self::Other(err.to_string())
    }
}

/// Gadget for a linear polynomial commitment verifier
pub trait PolynomialCommitmentVerifierGadget<
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G>,
>: Sized
{
    /// Gadget for the verifier key
    type VerifierKeyGadget: VerifierKeyGadget<PC::VerifierKey, ConstraintF>;
    /// Gadget for the state returned by verify functions
    type VerifierStateGadget: VerifierStateGadget<PC::VerifierState, ConstraintF>;
    /// Gadget for the commitment
    type CommitmentGadget: GroupGadget<PC::Commitment, ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>
        + AllocGadget<PC::Commitment, ConstraintF>;
    /// Gadget for the proof
    type ProofGadget: AllocGadget<PC::Proof, ConstraintF>;
    /// Gadget for the proof of multi_point openings
    type MultiPointProofGadget: MultiPointProofGadget<
        ConstraintF,
        G,
        PC::MultiPointProof,
        CommitmentGadget = Self::CommitmentGadget,
        ProofGadget = Self::ProofGadget,
    >;
    /// Gadget for the random oracle needed to get challenges
    type RandomOracleGadget: FiatShamirRngGadget<ConstraintF>;
    /// Error type
    type Error: 'static
        + From<SynthesisError>
        + From<PC::Error>
        + From<PolyError>
        + std::error::Error;

    /// this function specifies how to multiply a commitment to a challenge squeezed from the random oracle.
    /// Input parameter `challenge` must be an iterator over the bits of the challenge in *little-endian* order
    fn mul_by_challenge<
        'a,
        CS: ConstraintSystemAbstract<ConstraintF>,
        IT: Iterator<Item = &'a Boolean>,
    >(
        cs: CS,
        base: &Self::CommitmentGadget,
        challenge: IT,
    ) -> Result<Self::CommitmentGadget, SynthesisError> {
        safe_mul_bits::<ConstraintF, G, PC, Self, _, _>(cs, base, challenge)
    }
    /// This function specifies how to convert a challenge squeezed from the random oracle to a
    /// gadget for `G::ScalarField` with `challenge` as a *little-endian* representation
    fn challenge_to_non_native_field_element<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        challenge: &[Boolean],
    ) -> Result<NonNativeFieldGadget<G::ScalarField, ConstraintF>, SynthesisError> {
        NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(
            cs,
            challenge
                .iter()
                .rev()
                .cloned()
                .collect::<Vec<_>>()
                .as_slice(),
        )
    }

    /// Succinct check of the verify
    fn succinct_verify<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        vk: &Self::VerifierKeyGadget,
        commitment: &Self::CommitmentGadget,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        value: &Vec<Boolean>, // bits of evaluation point in big-endian order
        proof: &Self::ProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error>;

    /// succinct check of the verification of an opening proof for multiple polynomials in the
    /// same point
    fn succinct_verify_single_point_multi_poly<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &Self::VerifierKeyGadget,
        labeled_commitments: &[LabeledCommitmentGadget<Self, ConstraintF, G, PC>], //ToDo: see if we can take an impl IntoIterator as for the primitive
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        values: &[NonNativeFieldGadget<G::ScalarField, ConstraintF>],
        proof: &Self::ProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error> {
        let lambda = random_oracle.enforce_get_challenge::<_, 128>(
            cs.ns(|| "squeeze lambda for single-point-multi-poly verify"),
        )?;
        let lambda_non_native = Self::challenge_to_non_native_field_element(
            cs.ns(|| "convert lambda to non native field gadget"),
            &lambda,
        )?;
        /*
        Batching of commitments is performed with Horner scheme.
        That is, to compute a batched commitment C=C_1+lambda*C_2+lambda2*C_3+..+lambda^(n-1)*C_n from a set of commitments
        C_1,..,C_n we do as follows:
        - initialize C to C_n
        - for the commitment C_i,where i varies from n-1 to 1, we update C = C_i + lambda*C
        Therefore, we need to iterate the set of labeled commitments in reverse order.
        Same strategy is employed for values.
        */
        let mut commitments_iter = labeled_commitments.iter().rev();
        let mut batched_commitment = commitments_iter
            .next()
            .ok_or(SynthesisError::Other("no commitment provided".to_string()))?
            .commitment()
            .clone();

        let mut values_iter = values.iter().rev();
        let mut batched_value = values_iter
            .next()
            .ok_or(SynthesisError::Other("no evaluation provided".to_string()))?
            .clone();

        for (i, (commitment, value)) in commitments_iter.zip(values_iter).enumerate() {
            batched_commitment = Self::mul_by_challenge(
                cs.ns(|| format!("lambda*batched_commitment_{}", i)),
                &batched_commitment,
                lambda.iter(),
            )?;
            batched_commitment = batched_commitment.add(
                cs.ns(|| format!("add commitment {} to batched_commitment", i)),
                commitment.commitment(),
            )?;

            let batched_value_times_lambda = batched_value.mul_without_prereduce(
                cs.ns(|| format!("lambda*batched_value_{}", i)),
                &lambda_non_native,
            )?;
            //ToDo: This cast will be unnecessary after refactoring `NonNativeFieldGadget`
            let value = FromGadget::from(value, cs.ns(|| format!("value {} to mul result", i)))?;
            batched_value = batched_value_times_lambda
                .add(
                    cs.ns(|| format!("add value {} to batched_value", i)),
                    &value,
                )?
                .reduce(cs.ns(|| format!("reduce batched_value_{}", i)))?;
        }

        let batched_value_bits =
            batched_value.to_bits_for_normal_form(cs.ns(|| "batched value to bits"))?;

        Self::succinct_verify(
            &mut cs,
            &vk,
            &batched_commitment,
            point,
            &batched_value_bits,
            &proof,
            random_oracle,
        )
    }

    /// succinct check of the verification of an opening proof for multiple polynomials in
    /// multiple points
    fn succinct_verify_multi_poly_multi_point<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &Self::VerifierKeyGadget,
        labeled_commitments: &[LabeledCommitmentGadget<Self, ConstraintF, G, PC>],
        points: &QueryMap<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        values: &Evaluations<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        proof: &Self::MultiPointProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error> {
        let lambda_bits = random_oracle.enforce_get_challenge::<_, 128>(
            cs.ns(|| "squeezing random challenge for multi-point-multi-poly verify"),
        )?;

        random_oracle.enforce_record(
            cs.ns(|| "absorb commitment to polynomial h"),
            proof.get_h_commitment().clone(),
        )?;
        let evaluation_point_bits = random_oracle.enforce_get_challenge::<_, 128>(
            cs.ns(|| "squeeze evaluation point for multi-point multi-poly verify"),
        )?;
        let evaluation_point = Self::challenge_to_non_native_field_element(
            cs.ns(|| "evaluation point from squeezed bits"),
            &evaluation_point_bits,
        )?;

        let (mut batched_commitment, batched_value) = multi_poly_multi_point_batching(
            cs.ns(|| "multi point batching"),
            labeled_commitments,
            points,
            values,
            &evaluation_point,
            &lambda_bits,
        )?;

        batched_commitment =
            batched_commitment.sub(cs.ns(|| "sub h commitment"), &proof.get_h_commitment())?;
        let batched_value_bits =
            batched_value.to_bits_for_normal_form(cs.ns(|| "batched value to bits"))?;
        Self::succinct_verify(
            cs.ns(|| "succinct verify on batched"),
            &vk,
            &batched_commitment,
            &evaluation_point,
            &batched_value_bits,
            &proof.get_proof(),
            random_oracle,
        )
    }
}
