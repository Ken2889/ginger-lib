use crate::{Error as PolyError, Evaluations, PolynomialCommitment, QueryMap, PolynomialLabel};
use algebra::{Group, PrimeField};
use fiat_shamir::constraints::FiatShamirRngGadget;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::fields::{nonnative::nonnative_field_gadget::NonNativeFieldGadget, FieldGadget};
use r1cs_std::groups::GroupGadget;
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use r1cs_std::{alloc::AllocGadget, FromBitsGadget};
use std::collections:: HashMap;



pub mod data_structures;
pub use data_structures::*;

#[cfg(test)]
pub mod tests;
use r1cs_std::boolean::Boolean;
use r1cs_std::eq::EqGadget;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::FromGadget;

/// Default implementation of `succinct_verify_single_point_multi_poly` for `PolynomialCommitmentVerifierGadget`,
/// employed as a building block also by domain extended polynomial commitment gadget
pub(crate) fn single_point_multi_poly_succinct_verify<'a, ConstraintF, G, PC, PCG, CS, IC, IV>(
    mut cs: CS,
    vk: &PC::VerifierKey,
    labeled_commitments: IC,
    point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
    values: IV, //&[NonNativeFieldGadget<G::ScalarField, ConstraintF>],
    proof: &PCG::ProofGadget,
    random_oracle: &mut PCG::RandomOracleGadget,
) -> Result<PCG::VerifierStateGadget, PCG::Error>
    where
        ConstraintF: PrimeField,
        G: Group<BaseField = ConstraintF>,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
        CS: ConstraintSystemAbstract<ConstraintF>,
        IC: IntoIterator<
            Item = &'a LabeledCommitmentGadget<ConstraintF, PC::Commitment, PCG::CommitmentGadget>,
        >,
        <IC as IntoIterator>::IntoIter: DoubleEndedIterator,
        IV: IntoIterator<Item = &'a NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        <IV as IntoIterator>::IntoIter: DoubleEndedIterator,
{
    let lambda = random_oracle.enforce_get_challenge::<_, 128>(
        cs.ns(|| "squeeze lambda for single-point-multi-poly verify"),
    )?;
    let lambda_non_native = PCG::challenge_to_non_native_field_element(
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
    let mut commitments_iter = labeled_commitments.into_iter().rev();
    let mut batched_commitment = commitments_iter
        .next()
        .ok_or(SynthesisError::Other("no commitment provided".to_string()))?
        .commitment()
        .clone();

    let mut values_iter = values.into_iter().rev();
    let mut batched_value = values_iter
        .next()
        .ok_or(SynthesisError::Other("no evaluation provided".to_string()))?
        .clone();

    for (i, (commitment, value)) in commitments_iter.zip(values_iter).enumerate() {
        batched_commitment = PCG::mul_by_challenge(
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

    PCG::succinct_verify(
        &mut cs,
        vk,
        &batched_commitment,
        point,
        &batched_value_bits,
        &proof,
        random_oracle,
    )
}

/// Default implementation of `succinct_verify_multi_poly_multi_point` for `PolynomialCommitmentVerifierGadget`,
/// employed as a building block also by domain extended polynomial commitment gadget,
pub(crate) fn multi_poly_multi_point_succinct_verify<
    'a, 'b,
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
    CS: ConstraintSystemAbstract<ConstraintF>,
    QueryIT: IntoIterator<Item = (&'b super::PointLabel, &'b (NonNativeFieldGadget<G::ScalarField, ConstraintF>, LabelIT))>,
    LabelIT: 'b + IntoIterator<Item=PolynomialLabel> + Clone
>(
    mut cs: CS,
    vk: &PC::VerifierKey,
    commitment_map: HashMap<&'a PolynomialLabel, &'a LabeledCommitmentGadget<ConstraintF, PC::Commitment, PCG::CommitmentGadget>>,
    points: QueryIT,
    values: &Evaluations<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
    proof: &PCG::MultiPointProofGadget,
    random_oracle: &mut PCG::RandomOracleGadget,
) -> Result<PCG::VerifierStateGadget, PCG::Error>
where
    <QueryIT as IntoIterator>::IntoIter: DoubleEndedIterator,
    <LabelIT as IntoIterator>::IntoIter: DoubleEndedIterator,
{
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

    let evaluation_point = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::from_bits(
        cs.ns(|| "evaluation point to field gadget"),
        evaluation_point_bits
            .iter()
            .rev()
            .cloned()
            .collect::<Vec<_>>()
            .as_slice(),
    )?;


    let lambda = PCG::challenge_to_non_native_field_element(
        cs.ns(|| "convert lambda to non native field gadget"),
        &lambda_bits,
    )?;
    /*
    Given a set of points x_1, ..., x_n, an evaluation point x distinct from all the other
    points and m commitments C_1, ..., C_m of m polynomials, we need to compute a single batched
    commitment as follows. For a point x_i, consider the set S_i as the set of commitments of
    polynomials whose evaluation in x_i must be proven in this assertion.
    For each set S_i, we need to compute a batched commitment C'_i out of the C_{i,1}, ..., C_{i,m_i}
    commitments of S_i as C'_i = C_{i,1}+lambda*C_{i,2}+...+lambda^(m_i-1)*C_{i,m_i}. We do this with
    Horner scheme:
    - Initialize C'_i = C_{i,m_i}
    - For each commitment C_{i,j}, where j varies from m_i-1 to 1, we update C'_i = C_{i,j} + lambda*C'_i
    Therefore, for each set S_i we iterate over the commitments in reverse order,
    fetching the corresponding commitment from `commitment_map`.
    The same strategy is applied to batch values.
    Then, we combine commitments C'_i in a single commitment C by computing
    C=(x-x_1)^-1*C'_1 + ... + (x-x_n)^-1*C'_n
    */

    // batched_commitment and batched_value are initialized to None as in the first iteration
    // we need to proper initialize them
    let mut batched_commitment = None;
    let mut batched_value = None;

    for (point_label, (point, poly_labels)) in points.into_iter().rev() {
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
        // initialize batched_commitment and batched_value for the current point to properly
        // bootstrap the Horner scheme
        let mut labels_iter = poly_labels.clone().into_iter().rev();

        let label = labels_iter.next().ok_or(SynthesisError::Other(format!("no polynomial found for point with label {}", point_label)))?;
        let mut batched_commitment_for_point =
            (*commitment_map
                .get(&label)
                .ok_or(SynthesisError::Other(String::from(format!(
                    "commitment with label {} not found",
                    label
                ))))?).commitment().clone();
        let mut batched_value_for_point =
            values
                .get(&(label.clone(), point_label.clone()))
                .ok_or(SynthesisError::Other(String::from(format!(
                    "evaluation for label {}:{} not found",
                    label, point_label
                ))))?.clone();

        for label in labels_iter {
            let combined_label = format!("{}:{}", label, point_label); // unique label across all iterations obtained by combining label and point_label
            let commitment =
                (*commitment_map
                    .get(&label)
                    .ok_or(SynthesisError::Other(String::from(format!(
                        "commitment with label {} not found",
                        label
                    ))))?). commitment();
            let value =
                values
                    .get(&(label.clone(), point_label.clone()))
                    .ok_or(SynthesisError::Other(String::from(format!(
                        "evaluation for label {} not found",
                        combined_label
                    ))))?;

            let batched_commitment_times_lambda = PCG::mul_by_challenge(
                cs.ns(|| format!("batched_commitment*lambda for label {}", combined_label)),
                &batched_commitment_for_point,
                lambda_bits.iter(),
            )?;
            batched_commitment_for_point = batched_commitment_times_lambda.add(
                cs.ns(|| format!("add commitment for label {}", combined_label)),
                &commitment,
            )?;

            let batched_value_times_lambda = batched_value_for_point.mul_without_prereduce(
                cs.ns(|| format!("batched_value*lambda for label {}", combined_label)),
                &lambda,
            )?;
            //ToDo: This cast will be unnecessary after refactoring `NonNativeFieldGadget`
            let to_be_added_value = FromGadget::from(value, cs.ns(|| format!("value for label {} to mul result", combined_label)))?;
            batched_value_for_point = batched_value_times_lambda
                    .add(
                        cs.ns(|| {
                            format!("add value for point for label {}", combined_label)
                        }),
                        &to_be_added_value,
                    )?
                    .reduce(cs.ns(|| {
                        format!("reduce batched value for label {}", combined_label)
                    }))?;
        }
        batched_commitment_for_point = batched_commitment_for_point.mul_bits(
            cs.ns(|| format!("batched_commitment*z_i_over_z for point {}", point_label)),
            z_i_over_z_bits.iter().rev(), // must be reversed as mul_bits wants bits in little-endian
        )?;
        let batched_value_for_point = batched_value_for_point.mul_without_prereduce(
            cs.ns(|| format!("value*z_i_over_z for point {}", point_label)),
            &z_i_over_z_value,
        )?;
        match (batched_commitment, batched_value) {
            (None, None) => {
                batched_commitment = Some(batched_commitment_for_point);
                batched_value = Some(batched_value_for_point.reduce(cs.ns(|| format!("reduce batched_value for point {}", point_label)))?);
            },
            (Some(comm), Some(val)) => {
                batched_commitment = Some(comm.add(
                    cs.ns(|| format!("add batched_commitment for point {}", point_label)),
                    &batched_commitment_for_point,
                )?);

                let val_to_be_added = FromGadget::from(&val, cs.ns(|| format!("batched_value for point {} to mul result", point_label)))?;
                batched_value = Some(batched_value_for_point.add(
                    cs.ns(|| format!("add batched_value for point {}", point_label)),
                    &val_to_be_added,
                )?.reduce(cs.ns(|| format!("reduce batched_value for point {}", point_label)))?);
            },
            _ => unreachable!(),
        }

    }

    if batched_commitment.is_none() || batched_value.is_none() {
        Err(SynthesisError::Other(
            "no evaluation points provided".to_string(),
        ))?
    }

    let batched_commitment =
        batched_commitment.unwrap().sub(cs.ns(|| "sub h commitment"), &proof.get_h_commitment())?;
    let batched_value_bits =
        batched_value.unwrap().to_bits_for_normal_form(cs.ns(|| "batched value to bits"))?;

    PCG::succinct_verify(
        cs.ns(|| "succinct verify on batched"),
        &vk,
        &batched_commitment,
        &evaluation_point,
        &batched_value_bits,
        &proof.get_proof(),
        random_oracle,
    )
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
    /// Gadget for the state returned by verify functions
    type VerifierStateGadget: VerifierStateGadget<PC::VerifierState, ConstraintF>;
    /// Gadget for the commitment
    type CommitmentGadget: 'static
        + GroupGadget<PC::Commitment, ConstraintF>
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
        base.mul_bits(cs, challenge)
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
        vk: &PC::VerifierKey,
        commitment: &Self::CommitmentGadget,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        value: &Vec<Boolean>, // bits of evaluation point in big-endian order
        proof: &Self::ProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error>;

    /// succinct check of the verification of an opening proof for multiple polynomials in the
    /// same point
    fn succinct_verify_single_point_multi_poly<'a, CS, IC, IV>(
        cs: CS,
        vk: &PC::VerifierKey,
        labeled_commitments: IC,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        values: IV, //&[NonNativeFieldGadget<G::ScalarField, ConstraintF>],
        proof: &Self::ProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        IC: IntoIterator<
            Item = &'a LabeledCommitmentGadget<ConstraintF, PC::Commitment, Self::CommitmentGadget>,
        >,
        <IC as IntoIterator>::IntoIter: DoubleEndedIterator,
        IV: IntoIterator<Item = &'a NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        <IV as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        single_point_multi_poly_succinct_verify::<ConstraintF, G, PC, Self, _, _, _>(cs, vk, labeled_commitments, point, values, proof, random_oracle)
    }

    /// succinct check of the verification of an opening proof for multiple polynomials in
    /// multiple points
    fn succinct_verify_multi_poly_multi_point<'a, CS, I>(
        mut cs: CS,
        vk: &PC::VerifierKey,
        labeled_commitments: I,
        points: &QueryMap<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        values: &Evaluations<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        proof: &Self::MultiPointProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            I: IntoIterator<
                Item = &'a LabeledCommitmentGadget<ConstraintF, PC::Commitment, Self::CommitmentGadget>,
            >,
            <I as IntoIterator>::IntoIter: DoubleEndedIterator + Clone,
    {

        let commitment_map: HashMap<_, _> = labeled_commitments
            .into_iter()
            .map(|commitment| (commitment.label(), commitment))
            .collect();

        multi_poly_multi_point_succinct_verify::<ConstraintF, G, PC, Self, _, _, _>(
            cs.ns(|| "multi point batching"),
            vk,
            commitment_map,
            points,
            values,
            proof,
            random_oracle
        )
    }
}
