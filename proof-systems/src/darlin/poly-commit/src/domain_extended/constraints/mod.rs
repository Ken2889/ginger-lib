use std::collections::BTreeMap;
use crate::domain_extended::constraints::data_structures::DomainExtendedMultiPointProofGadget;
use crate::{DomainExtendedPolynomialCommitment, LabeledCommitmentGadget, PolynomialCommitment, PolynomialCommitmentVerifierGadget, VerifierKeyGadget, sort_commitments_and_values};
use algebra::{Group, PrimeField};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::boolean::Boolean;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::groups::group_vec::GroupGadgetVec;
use r1cs_std::prelude::GroupGadget;
use std::marker::PhantomData;
use crate::constraints::single_point_multi_poly_succinct_verify;

#[cfg(not(feature = "boneh-with-single-point-batch"))]
use crate::{multi_poly_multi_point_batching, QueryMap, Evaluations, MultiPointProofGadget, Error};
#[cfg(not(feature = "boneh-with-single-point-batch"))]
use fiat_shamir::constraints::FiatShamirRngGadget;
#[cfg(not(feature = "boneh-with-single-point-batch"))]
use r1cs_std::FromBitsGadget;
#[cfg(not(feature = "boneh-with-single-point-batch"))]
use std::collections::BTreeSet;

mod data_structures;

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
    fn combine_commitments<'a, CS, I>(
        mut cs: CS,
        vk: &PCG::VerifierKeyGadget,
        commitments: I,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
    ) -> Result<Vec<LabeledCommitmentGadget<ConstraintF, G, PCG::CommitmentGadget>>, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            I: IntoIterator<
                Item = &'a LabeledCommitmentGadget<
                    ConstraintF,
                    <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::Commitment,
                    <Self as PolynomialCommitmentVerifierGadget<ConstraintF, G, DomainExtendedPolynomialCommitment<G, PC>>>::CommitmentGadget,
                >,
            >,
    {
        let s = vk.degree() + 1;
        let point_to_s = point.pow_by_constant(cs.ns(|| "point^s"), [s as u64])?;
        let point_to_s_bits = point_to_s.to_bits_for_normal_form(cs.ns(|| "point^s to bits"))?;

        // iterators will contain the set of iterators, one for each polynomial with a segmented commitment
        let mut iterators = Vec::new();
        // labels will collect the labels of each of the polynomials
        let mut labels = Vec::new();
        for el in commitments {
            let cloned_el = el.clone();
            labels.push(cloned_el.label().clone());
            iterators.push(el.commitment().iter().rev());
        }
        /*for each polynomial with a segmented commitment C = {C_1, ..., C_m}, where m is the
        number of segments, we compute with Horner scheme a single combined commitment
        C' = C_1 + point_to_s*C_2 + point_to_s^2*C_3 + ... + point_to_s^(m-1)*C_m
        The combined commitments C' for all the polynomials will be collected in the `result` vector
        */
        let mut result = Vec::with_capacity(labels.len());
        for (i, (it, label)) in iterators.iter_mut().zip(labels.iter()).enumerate() {
            let mut combined_commitment = it
                .next()
                .ok_or(SynthesisError::Other(format!(
                    "no segmented commitments for polynomial with label {}",
                    label
                )))?
                .clone();
            for (j, comm) in it.enumerate() {
                combined_commitment = combined_commitment.mul_bits(
                    cs.ns(|| format!("point^s*commitment_{} for segmented commitment {}", j, i)),
                    point_to_s_bits.iter().rev(),
                )?;
                combined_commitment = combined_commitment.add(
                    cs.ns(|| format!("add commitment_{} for segmented commitment {}", j, i)),
                    comm,
                )?;
            }
            let labeled_commitment = LabeledCommitmentGadget::<
                ConstraintF,
                PC::Commitment,
                PCG::CommitmentGadget,
            >::new(label.clone(), combined_commitment);
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
    type VerifierKeyGadget = PCG::VerifierKeyGadget;
    type VerifierStateGadget = PCG::VerifierStateGadget;
    type CommitmentGadget = GroupGadgetVec<ConstraintF, PC::Commitment, PCG::CommitmentGadget>;
    type ProofGadget = PCG::ProofGadget;
    type MultiPointProofGadget = DomainExtendedMultiPointProofGadget<ConstraintF, G, PC, PCG>;
    type RandomOracleGadget = PCG::RandomOracleGadget;
    type Error = PCG::Error;

    fn mul_by_challenge<
        'a,
        CS: ConstraintSystemAbstract<ConstraintF>,
        IT: Iterator<Item = &'a Boolean>,
    >(
        mut cs: CS,
        base: &Self::CommitmentGadget,
        challenge: IT,
    ) -> Result<Self::CommitmentGadget, SynthesisError> {
        let mut mul_res = Vec::with_capacity(base.len());
        let challenge_bits = challenge.cloned().collect::<Vec<_>>();
        for (i, el) in base.iter().enumerate() {
            mul_res.push(PCG::mul_by_challenge(
                cs.ns(|| format!("multiply element {} by challenge", i)),
                &el,
                challenge_bits.iter(),
            )?);
        }
        Ok(Self::CommitmentGadget::new(mul_res))
    }

    fn challenge_to_non_native_field_element<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        challenge: &[Boolean],
    ) -> Result<NonNativeFieldGadget<G::ScalarField, ConstraintF>, SynthesisError> {
        PCG::challenge_to_non_native_field_element(cs, challenge)
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
        let labeled_commitment =
            LabeledCommitmentGadget::<
                ConstraintF,
                <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::Commitment,
                Self::CommitmentGadget,
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

    fn succinct_verify_single_point_multi_poly<'a, CS, IC, IV>(
        cs: CS,
        vk: &Self::VerifierKeyGadget,
        labeled_commitments: IC,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
        values: IV,
        proof: &Self::ProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            IC: IntoIterator<Item=&'a LabeledCommitmentGadget<ConstraintF,
                <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::Commitment,
                Self::CommitmentGadget>>,
            <IC as IntoIterator>::IntoIter: DoubleEndedIterator,
            IV: IntoIterator<Item=&'a NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
            <IV as IntoIterator>::IntoIter: DoubleEndedIterator {

        let (sorted_commitments, sorted_values) = sort_commitments_and_values!(labeled_commitments, values);

        single_point_multi_poly_succinct_verify::<ConstraintF, G, DomainExtendedPolynomialCommitment<G, PC>, Self, _, _ ,_>
            (cs, vk, sorted_commitments, point, sorted_values, proof, random_oracle)
    }


    /*// Override default implementation of PolynomialCommitmentVerifierGadget to combine the
    // commitments of the segments of each polynomial before batching the polynomials.
    // ToDo: remove if benchmarks show that this variant is outperformed
    #[cfg(not(feature = "boneh-with-single-point-batch"))]
    fn succinct_verify_multi_poly_multi_point<'a, CS, I>(
        mut cs: CS,
        vk: &Self::VerifierKeyGadget,
        labeled_commitments: I,
        points: &QueryMap<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        values: &Evaluations<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
        proof: &Self::MultiPointProofGadget,
        random_oracle: &mut Self::RandomOracleGadget,
    ) -> Result<Self::VerifierStateGadget, Self::Error>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        I: IntoIterator<
            Item = &'a LabeledCommitmentGadget<
                ConstraintF,
                <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::Commitment,
                Self::CommitmentGadget,
            >,
        >,
        <I as IntoIterator>::IntoIter: DoubleEndedIterator + Clone,
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

        let commitments_iter = labeled_commitments.into_iter();
        let commitments_iter_copy = commitments_iter.clone();

        let commitment_map: BTreeMap<_, _> = commitments_iter
            .map(|commitment| (commitment.label(), commitment.commitment()))
            .collect();

        let (sorted_query_map, values_for_sorted_map) = crate::sort_query_map!(points, commitment_map, (|comm: &Self::CommitmentGadget| comm.len()));

        let sorted_query_map_vec = sorted_query_map.into_iter().rev().map(|((_, point_label), value)| (point_label, &values_for_sorted_map[value])).collect::<Vec<_>>();

        // merge h-commitment to labeled_commitments to combine segments for all of them simultaneously
        let labeled_h_commitment = LabeledCommitmentGadget::<
            ConstraintF,
            <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::Commitment,
            Self::CommitmentGadget,
        >::new(
            String::from("labeled commitment"),
            proof.get_h_commitment().clone(),
        );
        let mut labeled_commitments_to_be_combined =
            commitments_iter_copy.collect::<Vec<_>>();
        labeled_commitments_to_be_combined.push(&labeled_h_commitment);
        let combined_commitments = Self::combine_commitments(
            cs.ns(|| "combine segmented commitments"),
            vk,
            labeled_commitments_to_be_combined,
            &evaluation_point,
        )?;
        let labeled_combined_h_commitment = combined_commitments
            .get(combined_commitments.len() - 1)
            .unwrap();

        let commitment_map: BTreeMap<_, _> = combined_commitments[..combined_commitments.len() - 1]
            .into_iter()
            .map(|commitment| (commitment.label(), commitment.commitment()))
            .collect();

        let (mut batched_commitment, batched_value) =
            multi_poly_multi_point_batching::<ConstraintF, G, PC, PCG, _, _, _>(
                cs.ns(|| "multi point batching"),
                commitment_map,
                sorted_query_map_vec,
                values,
                &evaluation_point,
                &lambda_bits,
            )?;

        // subtract h-commitment
        batched_commitment = batched_commitment.sub(
            cs.ns(|| "sub h commitment"),
            labeled_combined_h_commitment.commitment(),
        )?;
        let batched_value_bits =
            batched_value.to_bits_for_normal_form(cs.ns(|| "batched value to bits"))?;
        PCG::succinct_verify(
            cs.ns(|| "succinct verify on batched"),
            &vk,
            &batched_commitment,
            &evaluation_point,
            &batched_value_bits,
            &proof.get_proof(),
            random_oracle,
        )
    }*/

    // Override default implementation to process commitments with the optimal order depending on
    // the number of segments
    #[cfg(not(feature = "boneh-with-single-point-batch"))]
    fn succinct_verify_multi_poly_multi_point<'a, CS, I>(
     mut cs: CS,
     vk: &Self::VerifierKeyGadget,
     labeled_commitments: I,
     points: &QueryMap<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
     values: &Evaluations<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
     proof: &Self::MultiPointProofGadget,
     random_oracle: &mut Self::RandomOracleGadget)
        -> Result<Self::VerifierStateGadget, Self::Error>
        where CS: ConstraintSystemAbstract<ConstraintF>,
              I: IntoIterator<Item=&'a LabeledCommitmentGadget<
                  ConstraintF,
                  <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::Commitment,
                  Self::CommitmentGadget>>,
              <I as IntoIterator>::IntoIter: DoubleEndedIterator {
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

        let commitment_map: BTreeMap<_, _> = labeled_commitments
            .into_iter()
            .map(|commitment| (commitment.label(), commitment.commitment()))
            .collect();

        let (sorted_query_map, values_for_sorted_map) = crate::sort_query_map!(points, commitment_map, (|comm: &Self::CommitmentGadget| comm.len()));

        let sorted_query_map_vec = sorted_query_map.into_iter().rev().map(|((_, point_label), value)| (point_label, &values_for_sorted_map[value])).collect::<Vec<_>>();

        let (mut batched_commitment, batched_value) =
            multi_poly_multi_point_batching::<ConstraintF, G,
                DomainExtendedPolynomialCommitment<G, PC>,
                Self, _, _, _>(
                cs.ns(|| "multi point batching"),
                commitment_map,
                sorted_query_map_vec,
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
