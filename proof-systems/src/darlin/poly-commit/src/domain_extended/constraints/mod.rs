use crate::{safe_mul_bits, BDFGMultiPointProof, DomainExtendedPolynomialCommitment, Evaluations,
            LabeledCommitmentGadget, MultiPointProofGadget, PolynomialCommitment,
            PolynomialCommitmentVerifierGadget, QueryMap, VerifierKeyGadget};
use algebra::{Group, PrimeField};
//use fiat_shamir::constraints::FiatShamirRngGadget;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::alloc::AllocGadget;
use r1cs_std::boolean::Boolean;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::groups::group_vec::GroupGadgetVec;
use r1cs_std::prelude::GroupGadget;
use std::borrow::Borrow;
use std::collections::BTreeMap;
//use std::collections::BTreeMap;
use fiat_shamir::constraints::FiatShamirRngGadget;
use std::marker::PhantomData;

/// Gadget for multi-point proof for domain extended poly-commit verifier gadget
pub struct DomainExtendedMultiPointProofGadget<
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G, Commitment = G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
> {
    proof: PCG::Proof,
    h_commitment: GroupGadgetVec<ConstraintF, PC::Commitment, PCG::Commitment>,
}

impl<ConstraintF, G, PC, PCG>
    AllocGadget<
        <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::MultiPointProof,
        ConstraintF,
    > for DomainExtendedMultiPointProofGadget<ConstraintF, G, PC, PCG>
where
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: 'static + PolynomialCommitment<G, Commitment = G>,
    PCG: 'static + PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<
            <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::MultiPointProof,
        >,
    {
        let t = f()?;
        let mpp = t.borrow();

        let proof =
            PCG::Proof::alloc(cs.ns(|| "alloc single point proof"), || Ok(mpp.get_proof()))?;
        let h_commitment = GroupGadgetVec::<ConstraintF, PC::Commitment, PCG::Commitment>::alloc(
            cs.ns(|| "alloc h-commitment for multi-point proof"),
            || Ok(mpp.get_h_commitment().clone()),
        )?;
        Ok(Self {
            proof,
            h_commitment,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<
            <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::MultiPointProof,
        >,
    {
        let t = f()?;
        let mpp = t.borrow();

        let proof =
            PCG::Proof::alloc_input(cs.ns(|| "alloc single point proof"), || Ok(mpp.get_proof()))?;
        let h_commitment =
            GroupGadgetVec::<ConstraintF, PC::Commitment, PCG::Commitment>::alloc_input(
                cs.ns(|| "alloc h-commitment for multi-point proof"),
                || Ok(mpp.get_h_commitment().clone()),
            )?;
        Ok(Self {
            proof,
            h_commitment,
        })
    }
}

impl<ConstraintF, G, PC, PCG>
    MultiPointProofGadget<
        ConstraintF,
        G,
        <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::MultiPointProof,
    > for DomainExtendedMultiPointProofGadget<ConstraintF, G, PC, PCG>
where
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: 'static + PolynomialCommitment<G, Commitment = G>,
    PCG: 'static + PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
{
    type Commitment = GroupGadgetVec<ConstraintF, PC::Commitment, PCG::Commitment>;
    type Proof = PCG::Proof;

    fn get_proof(&self) -> &Self::Proof {
        &self.proof
    }
    fn get_h_commitment(&self) -> &Self::Commitment {
        &self.h_commitment
    }
}

/// Poly-commit verifier gadget for domain extended polynomials
pub struct DomainExtendedPolyCommitVerifierGadget<
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
> {
    _field: PhantomData<ConstraintF>,
    _curve: PhantomData<G>,
    _pc: PhantomData<PC>,
    _pcg: PhantomData<PCG>,
}

impl<
        ConstraintF: PrimeField,
        G: Group<BaseField = ConstraintF>,
        PC: 'static + PolynomialCommitment<G, Commitment = G>,
        PCG: 'static + PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
    > DomainExtendedPolyCommitVerifierGadget<ConstraintF, G, PC, PCG>
{
    // this function allows to convert the set of commitments of a segmented polynomial to a single commitment,
    // which can be used to verify an opening proof for the polynomial at point `point`.
    // For efficiency, the function allows to simultaneously convert set of commitments
    // for multiple segmented polynomials with an opening proof for the same point `point`.
    fn combine_commitments<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &PCG::VerifierKey,
        commitments: &[LabeledCommitmentGadget<
            Self,
            ConstraintF,
            G,
            DomainExtendedPolynomialCommitment<G, PC>,
        >],
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
    ) -> Result<Vec<LabeledCommitmentGadget<PCG, ConstraintF, G, PC>>, SynthesisError> {
        let s = vk.degree() + 1;
        let point_to_s = point.pow_by_constant(cs.ns(|| "point^s"), [s as u64])?;
        let point_to_s_bits = point_to_s.to_bits_for_normal_form(cs.ns(|| "point^s to bits"))?;

        let mut iterators = Vec::new();
        let mut labels = Vec::new();
        for el in commitments {
            let cloned_el = el.clone();
            labels.push(cloned_el.label().clone());
            iterators.push(el.commitment().iter().rev());
        }

        let zero_commitment = PCG::Commitment::zero(cs.ns(|| "alloc zero commitment"))?;
        let mut result = Vec::with_capacity(labels.len());
        for (i, (it, label)) in iterators.iter_mut().zip(labels.iter()).enumerate() {
            let mut combined_commitment = it.next().unwrap_or(&zero_commitment).clone();
            for (j, comm) in it.enumerate() {
                combined_commitment = safe_mul_bits::<ConstraintF, G, PC, PCG, _, _>(
                    cs.ns(|| format!("point^s*commitment_{} for segmented commitment {}", j, i)),
                    &combined_commitment,
                    point_to_s_bits.iter().rev(),
                )?;
                combined_commitment = combined_commitment.add(
                    cs.ns(|| format!("add commitment_{} for segmented commitment {}", j, i)),
                    comm,
                )?;
            }
            let labeled_commitment = LabeledCommitmentGadget::<PCG, ConstraintF, G, PC>::new(
                label.clone(),
                combined_commitment,
            );
            result.push(labeled_commitment)
        }

        Ok(result)
    }
}

impl<
        ConstraintF: PrimeField,
        G: Group<BaseField = ConstraintF>,
        PC: 'static + PolynomialCommitment<G, Commitment = G>,
        PCG: 'static + PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
    > PolynomialCommitmentVerifierGadget<ConstraintF, G, DomainExtendedPolynomialCommitment<G, PC>>
    for DomainExtendedPolyCommitVerifierGadget<ConstraintF, G, PC, PCG>
{
    type VerifierKey = PCG::VerifierKey;
    type VerifierState = PCG::VerifierState;
    type Commitment = GroupGadgetVec<ConstraintF, PC::Commitment, PCG::Commitment>;
    type Proof = PCG::Proof;
    type MultiPointProof = DomainExtendedMultiPointProofGadget<ConstraintF, G, PC, PCG>;
    type RandomOracle = PCG::RandomOracle;
    type Error = PCG::Error;

    fn mul_by_challenge<
        'a,
        CS: ConstraintSystemAbstract<ConstraintF>,
        IT: Iterator<Item = &'a Boolean>,
    >(
        mut cs: CS,
        base: &Self::Commitment,
        challenge: IT,
    ) -> Result<Self::Commitment, SynthesisError> {
        let mut mul_res = Vec::with_capacity(base.len());
        let challenge_bits = challenge.cloned().collect::<Vec<_>>();
        for (i, el) in base.iter().enumerate() {
            mul_res.push(PCG::mul_by_challenge(
                cs.ns(|| format!("multiply element {} by challenge", i)),
                &el,
                challenge_bits.iter(),
            )?);
        }
        Ok(Self::Commitment::new(mul_res))
    }

    fn challenge_to_non_native_field_element<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        challenge: &[Boolean],
    ) -> Result<NonNativeFieldGadget<G::ScalarField, ConstraintF>, SynthesisError> {
        PCG::challenge_to_non_native_field_element(cs, challenge)
    }

    fn succinct_verify<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &Self::VerifierKey,
        commitment: &Self::Commitment,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        value: &Vec<Boolean>,
        proof: &Self::Proof,
        random_oracle: &mut Self::RandomOracle,
    ) -> Result<Self::VerifierState, Self::Error> {
        let labeled_commitment =
            LabeledCommitmentGadget::<
                Self,
                ConstraintF,
                G,
                DomainExtendedPolynomialCommitment<G, PC>,
            >::new(String::from("labeled commitment"), commitment.clone());
        let labeled_combined_commitment = Self::combine_commitments(
            cs.ns(|| "combine segmented commitment"),
            vk,
            [labeled_commitment].as_ref(),
            point,
        )?;
        assert_eq!(labeled_combined_commitment.len(), 1);

        let combined_commitment = labeled_combined_commitment[0].commitment();

        PCG::succinct_verify(
            cs.ns(|| "verify proof over combined commitment for segmented polynomial"),
            vk,
            combined_commitment,
            point,
            value,
            proof,
            random_oracle,
        )
    }

    // Override default implementation of PolynomialCommitmentVerifierGadget to combine the
    // commitments of the segments of each polynomial before batching the polynomials.
    // ToDo: this implementation does not seem to outperform the default one except for few cases; therefore, it is left here as commented as in future we might run extensive benchmarks to determine the optimal strategy depending on the number of segments and the number of polynomials
    /*fn succinct_verify_single_point_multi_poly<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, vk: &Self::VerifierKey, labeled_commitments: &[LabeledCommitmentGadget<Self, ConstraintF, G, GG, DomainExtendedPolynomialCommitment<G, PC>>], point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>, values: &[NonNativeFieldGadget<G::ScalarField, ConstraintF>], proof: &Self::Proof, random_oracle: &mut Self::RandomOracle) -> Result<Self::VerifierState, Self::Error> {
        let combined_commitments = Self::combine_commitments(cs.ns(|| "combine segmented commitments"), vk, labeled_commitments, point)?;

        PCG::succinct_verify_single_point_multi_poly(cs.ns(|| ""), vk, combined_commitments.as_slice(), point, values, proof, random_oracle)
    }*/

    // Override default implementation of PolynomialCommitmentVerifierGadget to combine the
    // commitments of the segments of each polynomial before batching the polynomials.
    // ToDo: This implementation seems to be most efficient than default one in most of the cases, but extensive benchmarks may be necessary to determine the optimal strategy depending on the number of segments and the number of polynomials.
    fn succinct_verify_multi_poly_multi_point<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        vk: &Self::VerifierKey,
        labeled_commitments: &[LabeledCommitmentGadget<
            Self,
            ConstraintF,
            G,
            DomainExtendedPolynomialCommitment<G, PC>,
        >],
        points: &QueryMap<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        values: &Evaluations<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        proof: &Self::MultiPointProof,
        random_oracle: &mut Self::RandomOracle,
    ) -> Result<Self::VerifierState, Self::Error> {
        let lambda_bits = random_oracle.enforce_get_challenge::<_, 128>(
            cs.ns(|| "squeezing random challenge for multi-point-multi-poly verify"),
        )?;

        let lambda = Self::challenge_to_non_native_field_element(
            cs.ns(|| "convert lambda to non native field gadget"),
            &lambda_bits,
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

        // merge h-commitment to labeled_commitments to combine segments for all of them simultaneously
        let mut labeled_commitments_to_be_combined = vec![LabeledCommitmentGadget::<
            Self,
            ConstraintF,
            G,
            DomainExtendedPolynomialCommitment<G, PC>,
        >::new(
            String::from("labeled commitment"),
            proof.get_h_commitment().clone(),
        )];
        labeled_commitments_to_be_combined.extend_from_slice(labeled_commitments);
        let combined_commitments = Self::combine_commitments(
            cs.ns(|| "combine segmented commitments"),
            vk,
            labeled_commitments_to_be_combined.as_slice(),
            &evaluation_point,
        )?;
        let labeled_combined_h_commitment = combined_commitments.get(0).unwrap();

        let commitment_map: BTreeMap<_, _> = combined_commitments
            .iter()
            .skip(1) // skip first commitment as it is the h-commitment
            .map(|commitment| (commitment.label(), commitment.commitment()))
            .collect();

        let mut batched_commitment = None;
        let mut batched_value = None;

        for (point_label, (point, poly_labels)) in points.iter().rev() {
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
                let value = values.get(&(label.clone(), point_label.clone())).ok_or(
                    SynthesisError::Other(String::from(format!(
                        "evaluation for point {} not found",
                        point_label
                    ))),
                )?;

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
                            cs.ns(|| {
                                format!("batched_commitment*lambda for label {}", combined_label)
                            }),
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
        // subtract h-commitment
        let batched_commitment = batched_commitment.unwrap().sub(
            cs.ns(|| "sub h commitment"),
            labeled_combined_h_commitment.commitment(),
        )?;
        let batched_value_bits = batched_value
            .unwrap()
            .to_bits_for_normal_form(cs.ns(|| "batched value to bits"))?;
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
}
