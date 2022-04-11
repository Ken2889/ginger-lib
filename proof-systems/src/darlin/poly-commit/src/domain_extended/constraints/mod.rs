use crate::domain_extended::constraints::data_structures::DomainExtendedMultiPointProofGadget;
use crate::{DomainExtendedPolynomialCommitment, LabeledCommitmentGadget, PolynomialCommitment, PolynomialCommitmentVerifierGadget, sort_according_to_segments, PCKey};
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
use crate::{multi_poly_multi_point_succinct_verify, multi_point_with_sorted_query_map, QueryMap, Evaluations, Error};

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
        vk: &PC::VerifierKey,
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
        vk: &PC::VerifierKey,
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
        vk: &PC::VerifierKey,
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

        let (sorted_commitments, sorted_values) = sort_according_to_segments(labeled_commitments, values,
            |comm: &LabeledCommitmentGadget<ConstraintF,
                <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::Commitment,
                Self::CommitmentGadget>| comm.commitment().len(),
        |comm| comm.label());

        single_point_multi_poly_succinct_verify::<ConstraintF, G, DomainExtendedPolynomialCommitment<G, PC>, Self, _, _ ,_>
            (cs, vk, sorted_commitments, point, sorted_values, proof, random_oracle)
    }

    // Override default implementation to process commitments with the optimal order depending on
    // the number of segments
    #[cfg(not(feature = "boneh-with-single-point-batch"))]
    fn succinct_verify_multi_poly_multi_point<'a, CS, I>(
     mut cs: CS,
     vk: &PC::VerifierKey,
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

        multi_point_with_sorted_query_map(points, labeled_commitments,
  |comm: &LabeledCommitmentGadget<
                  ConstraintF,
                  <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::Commitment,
                  Self::CommitmentGadget>| comm.commitment().len(),
        |comm| comm.label(),

            |comm_map, sorted_query_map|
             multi_poly_multi_point_succinct_verify::<ConstraintF, G,
                DomainExtendedPolynomialCommitment<G, PC>,
                Self, _, _, _>(
                cs.ns(|| "multi point batching"),
                vk,
                comm_map,
                sorted_query_map,
                values,
                proof,
                random_oracle,
            ).map_err(|e | Error::Other(e.to_string()))
        ).map_err(|e| Self::Error::from(e))

    }
}
