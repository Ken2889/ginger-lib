use crate::{Error as PolyError, Evaluations, PCMultiPointProof, PCVerifierKey, PCVerifierState, PolynomialCommitment, PolynomialLabel, QueryMap};
use algebra::{EndoMulCurve, PrimeField};
use fiat_shamir::constraints::FiatShamirRngGadget;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::fields::{nonnative::nonnative_field_gadget::NonNativeFieldGadget, FieldGadget};
use r1cs_std::groups::{EndoMulCurveGadget, GroupGadget};
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use r1cs_std::{alloc::AllocGadget, FromBitsGadget, ToBitsGadget};
use rand::thread_rng;
use std::collections::BTreeMap;
use std::fmt::Debug;

#[cfg(test)]
pub mod tests;
use r1cs_std::boolean::Boolean;
use r1cs_std::eq::EqGadget;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::prelude::{CondSelectGadget, ConstantGadget};
use r1cs_std::uint8::UInt8;

/// A commitment gadget plus its label, needed for reference.
#[derive(Clone)]
pub struct LabeledCommitmentGadget<
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, PC>,
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
> {
    label: PolynomialLabel,
    commitment: PCG::Commitment,
}

impl<PCG, ConstraintF, G, GG, PC> LabeledCommitmentGadget<PCG, ConstraintF, G, GG, PC>
where
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, PC>,
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
{
    /// Instantiate a new labeled commitment from a label and a commitment gadget.
    pub fn new(label: PolynomialLabel, commitment: PCG::Commitment) -> Self {
        Self { label, commitment }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the commitment from `self`.
    pub fn commitment(&self) -> &PCG::Commitment {
        &self.commitment
    }
}

/// Define interface for a gadget representing an opening proof for a multi-point assertion
pub trait MultiPointProofGadget<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    MPP: PCMultiPointProof<G>,
>: AllocGadget<MPP, ConstraintF>
{
    /// Type of commitment gadget
    type Commitment;
    /// Type of the opening proof gadget for a single-point assertion
    type Proof;

    /// get the proof gadget for the combined single-point assertion
    fn get_proof(&self) -> &Self::Proof;

    /// get the commitment of polynomial h, which is computed in the opening proof of multi-point assertion
    fn get_h_commitment(&self) -> &Self::Commitment;
}

/// Gadget for the state returned by verifier in case of successful verification
pub trait VerifierStateGadget<VS: PCVerifierState, ConstraintF: PrimeField>:
    Clone + Debug + Eq + PartialEq + AllocGadget<VS, ConstraintF>
{
}
/// Interface for the gadget representing the verifier key
pub trait VerifierKeyGadget<VK: PCVerifierKey, ConstraintF: PrimeField>:
    Clone + Debug + Eq + PartialEq + AllocGadget<VK, ConstraintF>
{
    /// Get the maximum degree for a segment of a polynomial whose commitments can be verified
    /// with `self`
    fn segment_size(&self) -> usize;

    /// Get the gadget for the hash of the verifier key `VK` represented by `self`
    fn get_hash(&self) -> &Vec<UInt8>;
}

impl From<SynthesisError> for PolyError {
    fn from(err: SynthesisError) -> Self {
        Self::Other(err.to_string())
    }
}

pub(crate) fn safe_mul<'a, ConstraintF, G, GG, PC, PCG, CS, IT>(
    mut cs: CS,
    base_point: &PCG::Commitment,
    scalar: IT,
    endo_mul: bool,
) -> Result<PCG::Commitment, SynthesisError>
where
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, PC>,
    CS: ConstraintSystemAbstract<ConstraintF>,
    IT: Iterator<Item = &'a Boolean>,
{
    let rng = &mut thread_rng();
    let mut non_trivial_base_constant = G::rand(rng);
    while non_trivial_base_constant.is_zero() {
        non_trivial_base_constant = G::rand(rng);
    }
    let non_trivial_base_gadget = PCG::Commitment::from_value(
        cs.ns(|| "alloc non trivial base constant"),
        &non_trivial_base_constant,
    );
    let zero = PCG::Commitment::zero(cs.ns(|| "alloc constant 0"))?;

    let is_zero = base_point.is_zero(cs.ns(|| "check if base point is zero"))?;
    let non_trivial_base_point = PCG::Commitment::conditionally_select(
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
    PCG::Commitment::conditionally_select(
        cs.ns(|| "select correct result for safe mul"),
        &is_zero,
        &zero,
        &safe_mul_res,
    )
}

/// Gadget for a linear polynomial commitment verifier
pub trait PolynomialCommitmentVerifierGadget<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
>: Sized
{
    /// Gadget for the verifier key
    type VerifierKey: VerifierKeyGadget<PC::VerifierKey, ConstraintF>;
    /// Gadget for the state returned by verify functions
    type VerifierState: VerifierStateGadget<PC::VerifierState, ConstraintF>; //AllocGadget<PC::VerifierState, ConstraintF>;
    /// Gadget for the commitment
    type Commitment: EndoMulCurveGadget<G, ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>
        + AllocGadget<PC::Commitment, ConstraintF>;
    /// Gadget for the proof
    type Proof: AllocGadget<PC::Proof, ConstraintF>;
    /// Gadget for the proof of multi_point openings
    type MultiPointProof: MultiPointProofGadget<
        ConstraintF,
        G,
        PC::MultiPointProof,
        Commitment = Self::Commitment,
        Proof = Self::Proof,
    >;
    /// Gadget for the random oracle needed to get challenges
    type RandomOracle: FiatShamirRngGadget<ConstraintF>;
    /// Error type
    type Error: 'static
        + From<SynthesisError>
        + From<PC::Error>
        + From<PolyError>
        + std::error::Error;

    /// Succinct check of the verify
    fn succinct_verify<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        vk: &Self::VerifierKey,
        commitment: &Self::Commitment,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        value: &NonNativeFieldGadget<G::ScalarField, ConstraintF>, //ToDo: maybe this can be defined as Vec<Boolean> for efficiency
        proof: &Self::Proof,
        random_oracle: &mut Self::RandomOracle,
    ) -> Result<Self::VerifierState, Self::Error>;

    /// succinct check of the verification of an opening proof for multiple polynomials in the
    /// same point
    fn succinct_verify_single_point_multi_poly<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &Self::VerifierKey,
        labeled_commitments: &[LabeledCommitmentGadget<Self, ConstraintF, G, GG, PC>], //ToDo: see if we can take an impl IntoIterator as for the primitive
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

            batched_value = batched_value.mul(
                cs.ns(|| format!("lambda*batched_value_{}", i)),
                &lambda_non_native,
            )?;
            batched_value =
                batched_value.add(cs.ns(|| format!("add value {} to batched_value", i)), value)?;
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
        labeled_commitments: &[LabeledCommitmentGadget<Self, ConstraintF, G, GG, PC>],
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
            z_i_over_z_value.to_bits(cs.ns(|| "z_i_over_z_value to bits for last point"))?;

        let mut batched_commitment = safe_mul::<ConstraintF, G, GG, PC, Self, _, _>(
            cs.ns(|| "commitment*z_i_over_z for last point"),
            &commitment,
            z_i_over_z_bits.iter().rev(),
            false,
        )?;
        //let mut batched_commitment = commitment.mul_bits(cs.ns(|| "commitment*z_i_over_z for last point"), z_i_over_z_bits.iter().rev())?; // reverse order of bits since mul_bits requires little endian representation
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
                .to_bits(cs.ns(|| format!("z_i_over_z to bits for label {}", combined_label)))?;
            // z_i_over_z_bits.reverse(); // must be reversed as safe_mul wants bits in little-endian
            let to_be_added_commitment = safe_mul::<ConstraintF, G, GG, PC, Self, _, _>(
                cs.ns(|| format!("commitment*z_i_over_z for label {}", combined_label)),
                &commitment,
                z_i_over_z_bits.iter().rev(),
                false,
            )?;
            //let to_be_added_commitment = commitment.mul_bits(cs.ns(|| format!("commitment*z_i_over_z for label {}", combined_label)), z_i_over_z_bits.iter().rev())?;
            let to_be_added_value = value.mul(
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

            batched_value = batched_value.mul(
                cs.ns(|| format!("batched_value*lambda for label {}", combined_label)),
                &lambda,
            )?;
            batched_value = batched_value.add(
                cs.ns(|| format!("add value for point for label {}", combined_label)),
                &to_be_added_value,
            )?;
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
    }
}
