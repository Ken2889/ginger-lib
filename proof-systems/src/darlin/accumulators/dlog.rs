//! Halo's amortization strategy for the hard parts of the dlog/IPA commitment scheme
//! as separate public aggregation/accumulation scheme according to [BCMS20](https://eprint.iacr.org/2020/499).
//! The hard part consists of checking that the final committer key G_f (after all the
//! reduction steps) is the polynomial commitment of the succinct 'reduction polynomial'
//!     h(X) = (1 + xi_d * X^1)*(1 + xi_{d-1} * X^2) * ... (1 + xi_{1}*X^{2^d}),
//! where the xi_1,...,xi_d are the challenges of the dlog reduction.
use crate::darlin::accumulators::dual::{DualAccumulator, DualAccumulatorItem};
use crate::darlin::accumulators::{Accumulator, AccumulatorItem, Error, NonNativeItem};
use crate::darlin::accumulators::{BatchResult, BatchableAccumulator};
use crate::darlin::DomainExtendedIpaPc;
use algebra::serialize::*;
use algebra::{DensePolynomial, GroupVec, PrimeField, ToBits, ToConstraintField, UniformRand};
use bench_utils::*;
use fiat_shamir::{FiatShamirRng, FiatShamirRngSeed};
use num_traits::{One, Zero};
pub use poly_commit::ipa_pc::DLogItem;
use poly_commit::ipa_pc::{LabeledSuccinctCheckPolynomial, Proof, SuccinctCheckPolynomial};
use poly_commit::{
    ipa_pc::{CommitterKey, IPACurve, InnerProductArgPC, VerifierKey},
    Error as PCError, LabeledCommitment, PolynomialCommitment,
};
use rand::RngCore;

use rayon::prelude::*;
use std::marker::PhantomData;

pub struct DLogAccumulator<G, FS> {
    _group: PhantomData<G>,
    _fs_rng: PhantomData<FS>,
}

impl<G, FS> DLogAccumulator<G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng + 'static,
{
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"DL-ACC-2021";

    pub fn get_instance() -> Self {
        Self {
            _group: PhantomData,
            _fs_rng: PhantomData,
        }
    }

    /// This implementation handles the succinct verification of an aggregation proof
    /// for dlog "items".
    /// Recall that in the special situation of dlog items, the accumulated item
    /// is part of the proof itself. However, as we use size-optimized proofs, the
    /// check_poly are recomputed from the proof and returned by the verifier (if successful).
    pub fn succinct_verify_accumulated_items(
        vk: &VerifierKey<G>,
        previous_accumulators: Vec<DLogItem<G>>,
        proof: &AccumulationProof<G>,
    ) -> Result<Option<DLogItem<G>>, Error> {
        let succinct_time = start_timer!(|| "Succinct verify accumulate");

        let poly_time = start_timer!(|| "Compute Bullet Polys evaluations");

        // Initialize Fiat-Shamir rng
        let fs_rng_init_seed = {
            let mut seed_builder = FiatShamirRngSeed::new();
            seed_builder.add_bytes(&Self::PROTOCOL_NAME)?;
            seed_builder.add_bytes(&vk.hash)?;

            // NOTE: We assume the number of accumulators to be clear from the context.
            // As we use constant length encoding of field elements, we may use add_bytes()
            // without producing collisions in the serialization procedure.
            seed_builder.add_bytes(&previous_accumulators)?;
            seed_builder.finalize()?
        };
        let mut fs_rng = FS::from_seed(fs_rng_init_seed)?;

        // Sample a new challenge z
        let z = InnerProductArgPC::<G, FS>::challenge_to_scalar(
            fs_rng.get_challenge::<128>()?.to_vec(),
        )
        .map_err(|e| {
            end_timer!(poly_time);
            end_timer!(succinct_time);
            PCError::Other(e.to_string())
        })?;

        let comms_values = previous_accumulators
            .into_par_iter()
            .enumerate()
            .map(|(i, acc)| {
                let final_comm_key = acc.final_comm_key.clone();
                let check_poly = acc.check_poly;

                // Create a LabeledCommitment out of the final_comm_key
                let labeled_comm = {
                    let comm = final_comm_key;

                    LabeledCommitment::new(format!("check_poly_{}", i), GroupVec::new(vec![comm]))
                };

                // Compute the expected value, i.e. the value of the reduction polynomial at z.
                let eval = check_poly.evaluate(z);

                (labeled_comm, eval)
            })
            .collect::<Vec<_>>();

        // Save the evaluations into a separate vec
        let values = comms_values
            .iter()
            .map(|(_, val)| val.clone())
            .collect::<Vec<_>>();

        // Save comms into a separate vector
        let comms = comms_values
            .into_iter()
            .map(|(comm, _)| comm)
            .collect::<Vec<_>>();

        end_timer!(poly_time);

        let check_time = start_timer!(|| "Succinct check IPA proof");

        fs_rng.record(values.clone())?;

        // Succinctly verify the dlog opening proof,
        // and get the new reduction polynomial (the new xi's).
        let verifier_state = DomainExtendedIpaPc::<G, FS>::succinct_single_point_multi_poly_verify(
            vk,
            comms.iter(),
            z,
            values.iter(),
            &proof.pc_proof,
            &mut fs_rng,
        )
        .map_err(|e| {
            end_timer!(check_time);
            end_timer!(succinct_time);
            e
        })?;

        end_timer!(check_time);
        end_timer!(succinct_time);

        Ok(verifier_state)
    }
}

impl<G: IPACurve, FS: FiatShamirRng + 'static> Accumulator for DLogAccumulator<G, FS> {
    type ProverKey = CommitterKey<G>;
    type VerifierKey = <Self as BatchableAccumulator>::VerifierKey;
    type Proof = AccumulationProof<G>;
    type Item = DLogItem<G>;

    /// Batch verification of dLog items: combine reduction polynomials and their corresponding G_fins
    /// and perform a single MSM.
    fn check_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let check_time = start_timer!(|| "Check accumulators");

        let final_comm_keys = accumulators
            .iter()
            .map(|acc| acc.final_comm_key)
            .collect::<Vec<_>>();
        let xi_s_vec = accumulators
            .iter()
            .map(|acc| acc.check_poly.clone())
            .collect::<Vec<_>>();

        let batching_time = start_timer!(|| "Combine check polynomials and final comm keys");

        // Sample the batching challenge (using a cryptographically secure rng)
        let random_scalar = G::ScalarField::rand(rng);
        let mut batching_chal = G::ScalarField::one();

        // Collect the powers of the batching challenge in a vector
        let mut batching_chal_pows = vec![G::ScalarField::zero(); xi_s_vec.len()];
        for i in 0..batching_chal_pows.len() {
            batching_chal_pows[i] = batching_chal;
            batching_chal *= &random_scalar;
        }

        // Compute the linear combination of the reduction polys,
        //  h_bar(X) = sum_k lambda^k * h(xi's[k],X).
        let combined_check_poly = batching_chal_pows
            .par_iter()
            .zip(xi_s_vec)
            .map(|(&chal, check_poly)| {
                DensePolynomial::from_coefficients_vec(check_poly.compute_scaled_coeffs(-chal))
            })
            .reduce(
                || DensePolynomial::zero(),
                |acc, scaled_poly| &acc + &scaled_poly,
            );
        end_timer!(batching_time);

        // The dlog "hard part", checking that G_bar = sum_k lambda^k * G_f[k] == Comm(h_bar(X))
        // The equation to check would be:
        // lambda_1 * gfin_1 + ... + lambda_n * gfin_n - combined_h_1 * g_vk_1 - ... - combined_h_m * g_vk_m = 0
        // Where combined_h_i = lambda_1 * h_1_i + ... + lambda_n * h_n_i
        // We do final verification and the batching of the GFin in a single MSM
        let hard_time = start_timer!(|| "Batch verify hard parts");
        let final_val = InnerProductArgPC::<G, FS>::inner_commit(
            // The vk might be oversized, but the VariableBaseMSM function, will "trim"
            // the bases in order to be as big as the scalars vector, so no need to explicitly
            // trim the vk here.
            &[
                G::batch_normalization_into_affine(final_comm_keys)
                    .unwrap()
                    .as_slice(),
                vk.comm_key.as_slice(),
            ]
            .concat(),
            &[
                batching_chal_pows.as_slice(),
                combined_check_poly.coeffs.as_slice(),
            ]
            .concat(),
            None,
            None,
        )
        .map_err(|e| PCError::IncorrectInputLength(e.to_string()))?;
        end_timer!(hard_time);

        if !final_val.is_zero() {
            end_timer!(check_time);
            return Ok(false);
        }
        end_timer!(check_time);
        Ok(true)
    }

    /// Accumulate dlog "items" via the dlog amortization strategy:
    /// The given dlog items are challenged at a random query point and compared against
    /// the expected value. The item returned is a just the default dlog item to be discarded,
    /// the new "aggregated" dlog item is part of the aggregation proof itself.
    /// However, we do not explicitly provide the reduction challenges (the xi's) as they can
    /// be reconstructed from the proof.
    fn accumulate_items(
        ck: &Self::ProverKey,
        accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::Proof), Error> {
        let accumulate_time = start_timer!(|| "Accumulate");

        // Initialize Fiat-Shamir rng
        let fs_rng_init_seed = {
            let mut seed_builder = FiatShamirRngSeed::new();
            seed_builder.add_bytes(&Self::PROTOCOL_NAME)?;
            seed_builder.add_bytes(&ck.hash)?;
            // TODO: Shall we decompose this further when passing it to the seed builder ?
            seed_builder.add_bytes(&accumulators)?;
            seed_builder.finalize()?
        };
        let mut fs_rng = FS::from_seed(fs_rng_init_seed)?;

        // Sample a new challenge z
        let z = InnerProductArgPC::<G, FS>::challenge_to_scalar(
            fs_rng.get_challenge::<128>()?.to_vec(),
        )
        .map_err(|e| {
            end_timer!(accumulate_time);
            PCError::Other(e.to_string())
        })?;

        // Collect check_poly from the accumulators
        let check_poly = accumulators
            .iter()
            .enumerate()
            .map(|(i, acc)| {
                LabeledSuccinctCheckPolynomial::new(format!("check_poly_{}", i), &acc.check_poly)
            })
            .collect::<Vec<_>>();

        let poly_time = start_timer!(|| "Open Bullet Polys");

        // Compute multi-poly single-point opening proof for the G_f's, i.e.
        // the commitments of the item polys.
        let opening_proof = InnerProductArgPC::<G, FS>::open_reduction_polynomials(
            &ck,
            check_poly.iter(),
            z,
            &mut fs_rng,
        )
        .map_err(|e| {
            end_timer!(poly_time);
            end_timer!(accumulate_time);
            e
        })?;

        end_timer!(poly_time);

        // Even if our implementation is size optimized, the API requires us to
        // return an accumulator too: so we return a dummy one instead (to be
        // discarded by the caller).
        let accumulator = DLogItem::<G>::default();

        let mut accumulation_proof = AccumulationProof::<G>::default();
        // We consider the items to be accumulated as common inputs (of
        // the protocol), and the challenge z can be reconstructed from them,
        // hence the accumulation proof consists only of the dlog opening proof.
        accumulation_proof.pc_proof = opening_proof;

        end_timer!(accumulate_time);

        Ok((accumulator, accumulation_proof))
    }

    /// Full verification of an aggregation proof for dlog "items".
    /// Calls the succinct verifier and then does the remaining check of the aggregated item.
    fn verify_accumulated_items<R: RngCore>(
        _current_acc: &Self::Item,
        vk: &Self::VerifierKey,
        previous_accumulators: Vec<Self::Item>,
        proof: &Self::Proof,
        rng: &mut R,
    ) -> Result<bool, Error> {
        let check_acc_time = start_timer!(|| "Verify Accumulation");

        // Succinct part: verify the "easy" part of the aggregation proof
        let new_acc = Self::succinct_verify_accumulated_items(vk, previous_accumulators, proof)
            .map_err(|e| {
                end_timer!(check_acc_time);
                e
            })?;
        if new_acc.is_none() {
            end_timer!(check_acc_time);
            return Ok(false);
        }

        // Verify the aggregated accumulator
        let hard_time = start_timer!(|| "DLOG hard part");
        let result = Self::check_items::<R>(vk, &vec![new_acc.unwrap()], rng).map_err(|e| {
            end_timer!(hard_time);
            end_timer!(check_acc_time);
            e
        })?;
        end_timer!(hard_time);

        end_timer!(check_acc_time);

        Ok(result)
    }

    fn trivial_item(vk: &Self::VerifierKey) -> Result<Self::Item, Error> {
        // We define a trivial DLogAccumulator item as having all challenges equal to zero.
        // This corresponds to `check_poly` having degree-0 and being identically equal to one,
        // which in turn implies that the `final_comm_key` is equal to the first element of the
        // committer key.
        let check_poly = SuccinctCheckPolynomial::from_chals(vec![]);
        let final_comm_key = G::from_affine(&vk.comm_key[0]);
        Ok(Self::Item {
            check_poly,
            final_comm_key,
        })
    }

    fn random_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        let log_key_len = algebra::log2(vk.comm_key.len());
        let chals = (0..log_key_len as usize)
            .map(|_| u128::rand(rng).into())
            .collect();
        let check_poly = SuccinctCheckPolynomial::from_chals(chals);
        let final_comm_key = InnerProductArgPC::<G, FS>::inner_commit(
            vk.comm_key.as_slice(),
            check_poly.compute_coeffs().as_slice(),
            None,
            None,
        )
        .unwrap();

        Ok(Self::Item {
            check_poly,
            final_comm_key,
        })
    }

    fn invalid_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        let log_key_len = algebra::log2(vk.comm_key.len());
        let chals = (0..log_key_len as usize)
            .map(|_| u128::rand(rng).into())
            .collect();
        let check_poly = SuccinctCheckPolynomial::from_chals(chals);

        let final_comm_key = G::rand(rng);

        Ok(Self::Item {
            check_poly,
            final_comm_key,
        })
    }
}

impl<G: IPACurve, FS: FiatShamirRng + 'static> BatchableAccumulator for DLogAccumulator<G, FS> {
    type Group = G;
    type VerifierKey = VerifierKey<G>;
    type Item = DLogItem<G>;

    fn batch_items<R: RngCore>(
        _vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<BatchResult<G>, Error> {
        let compute_chals_time = start_timer!(|| "Compute batching challenges");
        let batching_chals = {
            let random_scalar = G::ScalarField::rand(rng);
            let num_batching_chals = accumulators.len();
            let mut batching_chals = Vec::with_capacity(num_batching_chals);
            let mut batching_chal = G::ScalarField::one();
            for _ in 0..num_batching_chals {
                batching_chals.push(batching_chal);
                batching_chal *= random_scalar;
            }
            batching_chals
        };
        end_timer!(compute_chals_time);

        let batch_time = start_timer!(|| "Batch commitments and polynomials");
        let (batched_commitment, batched_polynomial) = batching_chals
            .into_par_iter()
            .zip(accumulators.into_par_iter())
            .map(|(chal, item)| {
                (
                    item.final_comm_key * &chal,
                    DensePolynomial::from_coefficients_vec(
                        item.check_poly.compute_scaled_coeffs(chal),
                    ),
                )
            })
            .reduce(
                || (G::zero(), DensePolynomial::<G::ScalarField>::zero()),
                |a, b| (a.0 + b.0, a.1 + b.1),
            );
        end_timer!(batch_time);

        Ok(BatchResult {
            batched_commitment,
            batched_polynomial,
        })
    }
}

/// General struct of an aggregation proof. Typically, such proof stems from an
/// interactive oracle protocol (IOP) and a polynomial commitment scheme.
#[derive(Clone, Default, Debug, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccumulationProof<G: IPACurve> {
    /// Commitments to the polynomials produced by the prover.
    pub commitments: Vec<Vec<G>>,
    /// Evaluations of these polynomials.
    pub evaluations: Vec<G::ScalarField>,
    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: Proof<G>,
}

impl<G: IPACurve> AccumulatorItem for DLogItem<G> {
    type Group = G;
}

impl<'a, G: IPACurve> ToConstraintField<G::BaseField> for NonNativeItem<'a, DLogItem<G>> {
    fn to_field_elements(&self) -> Result<Vec<G::BaseField>, Error> {
        let mut fes = Vec::new();

        // The final_comm_key already consists of elements belonging to G::BaseField.
        let final_comm_key = self.0.final_comm_key.clone();
        fes.append(&mut final_comm_key.to_field_elements()?);

        // Convert the challenges of check_poly, which are 128 bit elements from G::ScalarField,
        // into a bit vector, then pack the full bit vector into G::BaseField elements as efficient
        // as possible (yet still secure).
        let to_skip = <G::ScalarField as PrimeField>::size_in_bits() - 128;
        let mut check_poly_bits = Vec::new();
        for fe in self.0.check_poly.chals.iter() {
            let bits = fe.write_bits();
            // write_bits() outputs a Big Endian bit order representation of fe and the same
            // expects [bool].to_field_elements(): therefore we need to take the last 128 bits,
            // e.g. we need to skip the first MODULUS_BITS - 128 bits.
            debug_assert!(
                <[bool] as ToConstraintField<G::ScalarField>>::to_field_elements(&bits[to_skip..])
                    .unwrap()[0]
                    == *fe
            );
            check_poly_bits.extend_from_slice(&bits[to_skip..]);
        }
        fes.append(&mut check_poly_bits.to_field_elements()?);

        Ok(fes)
    }
}

pub type DualDLogAccumulator<'a, G1, G2, FS> =
    DualAccumulator<'a, DLogAccumulator<G1, FS>, DLogAccumulator<G2, FS>>;
pub type DualDLogItem<G1, G2> = DualAccumulatorItem<DLogItem<G1>, DLogItem<G2>>;

#[cfg(test)]
mod test {
    use super::*;
    use algebra::{test_canonical_serialize_deserialize, DualCycle, SemanticallyValid};
    use blake2::Blake2s;
    use derivative::Derivative;
    use digest::Digest;
    use poly_commit::{
        ipa_pc::Proof, DomainExtendedMultiPointProof, Evaluations, LabeledPolynomial, PCKey,
        PolynomialCommitment, QueryMap,
    };
    use rand::{distributions::Distribution, thread_rng, Rng};
    use std::marker::PhantomData;

    fn get_test_fs_rng<G: IPACurve, FS: FiatShamirRng>() -> FS {
        let mut seed_builder = FiatShamirRngSeed::new();
        seed_builder.add_bytes(b"TEST_SEED").unwrap();
        let fs_rng_seed = seed_builder.finalize().unwrap();
        FS::from_seed(fs_rng_seed).unwrap()
    }

    #[derive(Copy, Clone, Default)]
    struct TestInfo {
        max_degree: Option<usize>,
        supported_degree: Option<usize>,
        num_polynomials: usize,
        hiding: bool,
        max_num_queries: usize,
        segmented: bool,
    }

    #[derive(Derivative)]
    #[derivative(Clone(bound = ""))]
    struct VerifierData<'a, G: IPACurve> {
        vk: VerifierKey<G>,
        comms: Vec<LabeledCommitment<GroupVec<G>>>,
        query_map: QueryMap<'a, G::ScalarField>,
        values: Evaluations<'a, G::ScalarField>,
        proof: DomainExtendedMultiPointProof<G, Proof<G>>,
        polynomials: Vec<LabeledPolynomial<G::ScalarField>>,
        num_polynomials: usize,
        num_points_in_query_map: usize,
        _m: PhantomData<&'a G::ScalarField>, // To avoid compilation issue 'a
    }

    // Samples a random instance of a dlog multi-point multi-poly opening proof according to the
    // specifications in the TestInfo.
    fn get_data_for_verifier<'a, G, D, FS>(
        info: TestInfo,
        ck: Option<CommitterKey<G>>,
    ) -> Result<VerifierData<'a, G>, Error>
    where
        G: IPACurve,
        D: Digest + 'static,
        FS: FiatShamirRng + 'static,
    {
        let TestInfo {
            max_degree,       // maximum degree supported by the dlog commitment scheme
            supported_degree, // the supported maximum degree after trimming
            num_polynomials,  // number of random polynomials involved in the opening proof
            max_num_queries,  // size of the random query set for the opening proof
            segmented,        // use segmentation or not
            hiding,           // hiding or not
            ..
        } = info;

        let rng = &mut thread_rng();
        let max_degree =
            max_degree.unwrap_or(rand::distributions::Uniform::from(2..=64).sample(rng));
        let ck = if ck.is_some() {
            ck.unwrap()
        } else {
            DomainExtendedIpaPc::<G, FS>::setup::<D>(max_degree)?.0
        };

        test_canonical_serialize_deserialize(true, &ck);

        let supported_degree = match supported_degree {
            Some(0) => 0,
            Some(d) => d,
            None => rand::distributions::Uniform::from(1..=max_degree).sample(rng),
        };
        assert!(
            max_degree >= supported_degree,
            "max_degree < supported_degree"
        );
        let mut polynomials = Vec::new();

        // random degree multiplier when using segementation
        let seg_mul = rand::distributions::Uniform::from(5..=15).sample(rng);

        let mut poly_labels = Vec::new();
        println!("Sampled supported degree");

        // Generate random dense polynomials
        let num_points_in_query_map =
            rand::distributions::Uniform::from(1..=max_num_queries).sample(rng);
        for i in 0..num_polynomials {
            let poly_label = format!("Test{}", i);
            poly_labels.push(poly_label.clone());
            let degree;
            if segmented {
                degree = if supported_degree > 0 {
                    rand::distributions::Uniform::from(1..=supported_degree).sample(rng)
                } else {
                    0
                } * seg_mul;
            } else {
                degree = if supported_degree > 0 {
                    rand::distributions::Uniform::from(1..=supported_degree).sample(rng)
                } else {
                    0
                }
            }
            let poly = DensePolynomial::rand(degree, rng);

            polynomials.push(LabeledPolynomial::new(poly_label, poly, hiding))
        }
        println!("supported degree: {:?}", supported_degree);
        println!("num_points_in_query_map: {:?}", num_points_in_query_map);

        let ck = ck.trim(supported_degree)?;
        println!("Trimmed");

        test_canonical_serialize_deserialize(true, &ck);

        let (comms, rands) =
            DomainExtendedIpaPc::<G, FS>::commit_many(&ck, &polynomials, Some(rng))?;

        // Evaluate all polynomials in all points
        let mut query_map = QueryMap::new();
        let mut values = Evaluations::new();
        // let mut point = F::one();
        for i in 0..num_points_in_query_map {
            let point = G::ScalarField::rand(rng);
            let point_label = format!("{}", i);
            query_map.insert(
                point_label.clone(),
                (point, poly_labels.iter().cloned().collect()),
            );
            for poly in polynomials.iter() {
                let value = poly.evaluate(point);
                values.insert((poly.label().clone(), point_label.clone()), value);
            }
        }

        let mut fs_rng = get_test_fs_rng::<G, FS>();
        let proof = DomainExtendedIpaPc::<G, FS>::multi_point_multi_poly_open(
            &ck,
            &polynomials,
            &query_map,
            &mut fs_rng,
            &rands,
            Some(rng),
        )?;

        test_canonical_serialize_deserialize(true, &proof);

        Ok(VerifierData {
            vk: ck,
            comms,
            query_map,
            values,
            proof,
            polynomials,
            num_polynomials,
            num_points_in_query_map,
            _m: PhantomData,
        })
    }

    // We sample random instances of multi-point multi-poly dlog opening proofs,
    // produce aggregation proofs for their dlog items and fully verify these aggregation proofs.
    fn accumulation_test<G, D, FS>() -> Result<(), Error>
    where
        G: IPACurve,
        D: Digest + 'static,
        FS: FiatShamirRng + 'static,
    {
        let rng = &mut thread_rng();
        let max_degree = rand::distributions::Uniform::from(2..=128).sample(rng);

        let mut info = TestInfo {
            max_degree: Some(max_degree),
            supported_degree: None,
            num_polynomials: 10,
            max_num_queries: 5,
            ..Default::default()
        };

        let (_, vk) = DomainExtendedIpaPc::<G, FS>::setup::<D>(max_degree)?;

        test_canonical_serialize_deserialize(true, &vk);

        let vk = vk.trim(max_degree)?;

        test_canonical_serialize_deserialize(true, &vk);

        for num_proofs in 1..20 {
            let mut verifier_data_vec = Vec::with_capacity(num_proofs);

            // Generate all proofs and the data needed by the verifier to verify them
            for _ in 0..num_proofs {
                // Modify requirements at random
                info.hiding = rng.gen();
                info.segmented = rng.gen();
                verifier_data_vec
                    .push(get_data_for_verifier::<G, D, FS>(info, Some(vk.clone())).unwrap())
            }

            let mut comms = Vec::new();
            let mut query_maps = Vec::new();
            let mut evals = Vec::new();
            let mut proofs = Vec::new();
            let mut states = Vec::new();

            let state = get_test_fs_rng::<G, FS>().get_state().clone();

            verifier_data_vec.iter().for_each(|verifier_data| {
                let len = verifier_data.vk.comm_key.len();
                assert_eq!(&verifier_data.vk.comm_key[..], &vk.comm_key[..len]); // Vk should be equal for all proofs
                comms.push(verifier_data.comms.as_slice());
                query_maps.push(&verifier_data.query_map);
                evals.push(&verifier_data.values);
                proofs.push(&verifier_data.proof);
                states.push(&state);
            });

            // extract the xi's and G_fin's from the proof
            let accumulators = DomainExtendedIpaPc::<G, FS>::batch_succinct_verify(
                &vk,
                comms.clone(),
                query_maps.clone(),
                evals.clone(),
                proofs.clone(),
                states.clone(),
            )?;

            test_canonical_serialize_deserialize(true, &accumulators);
            assert!(accumulators.is_valid());

            // provide aggregation proof of the extracted dlog items
            let (_, proof) = DLogAccumulator::<G, FS>::accumulate_items(&vk, accumulators.clone())?;

            test_canonical_serialize_deserialize(true, &proof);

            // Verifier side
            let dummy = DLogItem::<G>::default();
            assert!(DLogAccumulator::<G, FS>::verify_accumulated_items(
                &dummy,
                &vk,
                // Actually the verifier should recompute the accumulators with the succinct verification
                accumulators,
                &proof,
                rng
            )?);
        }
        Ok(())
    }

    // We sample random instances of multi-point multi-poly dlog opening proofs,
    // and batch verify their dlog items.
    fn batch_verification_test<G, D, FS>() -> Result<(), Error>
    where
        G: IPACurve,
        D: Digest + 'static,
        FS: FiatShamirRng + 'static,
    {
        let rng = &mut thread_rng();
        let max_degree = rand::distributions::Uniform::from(2..=128).sample(rng);

        let mut info = TestInfo {
            max_degree: Some(max_degree),
            supported_degree: None,
            num_polynomials: 10,
            max_num_queries: 5,
            ..Default::default()
        };

        let (_, vk) = DomainExtendedIpaPc::<G, FS>::setup::<D>(max_degree)?;
        let vk = vk.trim(max_degree)?;

        test_canonical_serialize_deserialize(true, &vk);

        for num_proofs in 1..20 {
            let mut verifier_data_vec = Vec::with_capacity(num_proofs);

            // Generate all proofs and the data needed by the verifier to verify them
            for _ in 0..num_proofs {
                // Modify requirements at random
                info.hiding = rng.gen();
                info.segmented = rng.gen();
                verifier_data_vec
                    .push(get_data_for_verifier::<G, D, FS>(info, Some(vk.clone())).unwrap())
            }

            let mut comms = Vec::new();
            let mut query_maps = Vec::new();
            let mut evals = Vec::new();
            let mut proofs = Vec::new();
            let mut states = Vec::new();

            let state = get_test_fs_rng::<G, FS>().get_state().clone();

            verifier_data_vec.iter().for_each(|verifier_data| {
                let len = verifier_data.vk.comm_key.len();
                assert_eq!(&verifier_data.vk.comm_key[..], &vk.comm_key[..len]); // Vk should be equal for all proofs
                comms.push(verifier_data.comms.as_slice());
                query_maps.push(&verifier_data.query_map);
                evals.push(&verifier_data.values);
                proofs.push(&verifier_data.proof);
                states.push(&state);
            });

            // extract the xi's and G_fin's from the proof
            let accumulators = DomainExtendedIpaPc::<G, FS>::batch_succinct_verify(
                &vk,
                comms.clone(),
                query_maps.clone(),
                evals.clone(),
                proofs.clone(),
                states.clone(),
            )?;

            test_canonical_serialize_deserialize(true, &accumulators);
            assert!(accumulators.is_valid());

            // batch verify the extracted dlog items
            assert!(DLogAccumulator::<G, FS>::check_items(
                &vk,
                &accumulators,
                rng
            )?);
        }
        Ok(())
    }

    use crate::darlin::accumulators::tests::{get_committer_key, test_check_items};
    use algebra::curves::tweedle::{
        dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum,
    };

    fn test_dlog_check_items<G1, G2, FS, D>(pc_max_degree: usize, num_items: usize)
    where
        G1: IPACurve,
        G2: IPACurve,
        G1: DualCycle<G2>,
        FS: FiatShamirRng + 'static,
        D: Digest,
    {
        let rng = &mut thread_rng();
        let vk_g1 = get_committer_key::<G1, FS, D>(pc_max_degree);
        let vk_g2 = get_committer_key::<G2, FS, D>(pc_max_degree);

        test_check_items::<DLogAccumulator<G1, FS>, _>(&vk_g1, num_items, rng);

        test_check_items::<DualDLogAccumulator<G1, G2, FS>, _>(&(&vk_g1, &vk_g2), num_items, rng);
    }

    #[cfg(not(feature = "circuit-friendly"))]
    mod chacha_fs {
        use super::*;
        use fiat_shamir::chacha20::FiatShamirChaChaRng;

        #[test]
        fn test_tweedle_accumulate_verify() {
            accumulation_test::<TweedleDee, Blake2s, FiatShamirChaChaRng<Blake2s>>().unwrap();
            accumulation_test::<TweedleDum, Blake2s, FiatShamirChaChaRng<Blake2s>>().unwrap();
        }

        #[test]
        fn test_tweedle_batch_verify() {
            batch_verification_test::<TweedleDee, Blake2s, FiatShamirChaChaRng<Blake2s>>().unwrap();
            batch_verification_test::<TweedleDum, Blake2s, FiatShamirChaChaRng<Blake2s>>().unwrap();
        }

        #[test]
        fn test_tweedle_dlog_check_items() {
            test_dlog_check_items::<TweedleDee, TweedleDum, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                127, 10,
            );
            test_dlog_check_items::<TweedleDum, TweedleDee, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                127, 10,
            );
        }
    }

    #[cfg(feature = "circuit-friendly")]
    mod poseidon_fs {
        use super::*;
        use fiat_shamir::poseidon::{TweedleFqPoseidonFSRng, TweedleFrPoseidonFSRng};

        #[test]
        fn test_tweedle_accumulate_verify() {
            accumulation_test::<TweedleDee, Blake2s, TweedleFqPoseidonFSRng>().unwrap();
            accumulation_test::<TweedleDum, Blake2s, TweedleFrPoseidonFSRng>().unwrap();
        }

        #[test]
        fn test_tweedle_batch_verify() {
            batch_verification_test::<TweedleDee, Blake2s, TweedleFqPoseidonFSRng>().unwrap();
            batch_verification_test::<TweedleDum, Blake2s, TweedleFrPoseidonFSRng>().unwrap();
        }

        #[test]
        fn test_tweedle_dlog_check_items() {
            test_dlog_check_items::<TweedleDee, TweedleDum, TweedleFqPoseidonFSRng, Blake2s>(
                127, 10,
            );
            test_dlog_check_items::<TweedleDum, TweedleDee, TweedleFrPoseidonFSRng, Blake2s>(
                127, 10,
            );
        }
    }
}
