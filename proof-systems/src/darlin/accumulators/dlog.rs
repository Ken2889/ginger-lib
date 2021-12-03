//! Halo's amortization strategy for the hard parts of the dlog/IPA commitment scheme
//! as separate public aggregation/accumulation scheme according to [BCMS20](https://eprint.iacr.org/2020/499).
//! The hard part consists of checking that the final committer key G_f (after all the
//! reduction steps) is the polynomial commitment of the succinct 'reduction polynomial'
//!     h(X) = (1 + xi_d * X^1)*(1 + xi_{d-1} * X^2) * ... (1 + xi_{1}*X^{2^d}),
//! where the xi_1,...,xi_d are the challenges of the dlog reduction.
use crate::darlin::accumulators::{AccumulationProof, ItemAccumulator};
use algebra::polynomial::DensePolynomial as Polynomial;
use algebra::{
    Group, GroupVec, Field, Curve,
    serialize::*, to_bytes, SemanticallyValid, ToBytes,
    UniformRand,
};
use digest::Digest;
use poly_commit::{
    fiat_shamir_rng::{FiatShamirRng, FiatShamirRngSeed},
    ipa_pc::{CommitterKey, InnerProductArgPC, SuccinctCheckPolynomial, VerifierKey},
    DomainExtendedPolynomialCommitment, Error, LabeledCommitment,
    PolynomialCommitment,
};
use rand::RngCore;
use rayon::prelude::*;
use std::marker::PhantomData;

/// This implements the public aggregator for the IPA/DLOG commitment scheme.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DLogItem<G: Curve> {
    /// Final committer key after the DLOG reduction.
    pub(crate) g_final: GroupVec<G>,

    /// Challenges of the DLOG reduction.
    pub(crate) xi_s: SuccinctCheckPolynomial<G::ScalarField>,
}

impl<G: Curve> CanonicalSerialize for DLogItem<G> {
    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // GFinal will always be 1 segment and without any shift
        CanonicalSerialize::serialize(&self.g_final[0], &mut writer)?;

        CanonicalSerialize::serialize(&self.xi_s, &mut writer)
    }

    fn serialized_size(&self) -> usize {
        self.g_final[0].serialized_size() + self.xi_s.serialized_size()
    }

    fn serialize_without_metadata<W: Write>(
        &self,
        mut writer: W,
    ) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize_without_metadata(&self.g_final[0], &mut writer)?;

        CanonicalSerialize::serialize_without_metadata(&self.xi_s, &mut writer)
    }

    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // GFinal will always be 1 segment and without any shift
        CanonicalSerialize::serialize_uncompressed(&self.g_final[0], &mut writer)?;

        CanonicalSerialize::serialize_uncompressed(&self.xi_s, &mut writer)
    }

    fn uncompressed_size(&self) -> usize {
        self.g_final[0].uncompressed_size() + self.xi_s.uncompressed_size()
    }
}

impl<G: Curve> CanonicalDeserialize for DLogItem<G> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // GFinal will always be 1 segment and without any shift
        let g_final =
            GroupVec::new(vec![CanonicalDeserialize::deserialize(&mut reader)?]);

        let xi_s = CanonicalDeserialize::deserialize(&mut reader)?;

        Ok(Self { g_final, xi_s })
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // GFinal will always be 1 segment and without any shift
        let g_final =
            GroupVec::new(vec![CanonicalDeserialize::deserialize_unchecked(
                &mut reader,
            )?]);

        let xi_s = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        Ok(Self { g_final, xi_s })
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // GFinal will always be 1 segment and without any shift
        let g_final =
            GroupVec::new(vec![CanonicalDeserialize::deserialize_uncompressed(
                &mut reader,
            )?]);

        let xi_s = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        Ok(Self { g_final, xi_s })
    }

    #[inline]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        // GFinal will always be 1 segment and without any shift
        let g_final = GroupVec::new(vec![
            CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?,
        ]);

        let xi_s = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        Ok(Self { g_final, xi_s })
    }
}

impl<G: Curve> SemanticallyValid for DLogItem<G> {
    fn is_valid(&self) -> bool {
        self.g_final.is_valid() && self.g_final.len() == 1 && self.xi_s.0.is_valid()
    }
}

impl<G: Curve> Default for DLogItem<G> {
    fn default() -> Self {
        Self {
            g_final: GroupVec::<G>::default(),
            xi_s: SuccinctCheckPolynomial(vec![]),
        }
    }
}

impl<G: Curve> ToBytes for DLogItem<G> {
    fn write<W: Write>(&self, writer: W) -> std::io::Result<()> {
        use std::io::{Error, ErrorKind};

        self.serialize_without_metadata(writer)
            .map_err(|e| Error::new(ErrorKind::Other, format! {"{:?}", e}))
    }
}

pub struct DLogItemAccumulator<G: Curve, D: Digest + 'static> {
    _digest: PhantomData<D>,
    _group: PhantomData<G>,
}

impl<G: Curve, D: Digest + 'static> DLogItemAccumulator<G, D> {
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"DL-ACC-2021";

    pub fn get_instance() -> Self {
        Self {
            _group: PhantomData,
            _digest: PhantomData,
        }
    }

    /// This implementation handles the succinct verification of an aggregation proof
    /// for dlog "items".
    /// Recall that in the special situation of dlog items, the accumulated item
    /// is part of the proof itself. However, as we use size-optimized proofs, the
    /// xi_s are recomputed from the proof and returned by the verifier (if successful).
    pub fn succinct_verify_accumulated_items(
        vk: &VerifierKey<G>,
        previous_accumulators: Vec<DLogItem<G>>,
        proof: &AccumulationProof<G>,
    ) -> Result<Option<DLogItem<G>>, Error> {
        let succinct_time = start_timer!(|| "Succinct verify accumulate");

        let poly_time = start_timer!(|| "Compute Bullet Polys evaluations");

        // Initialize Fiat-Shamir rng
        let fs_rng_init_seed = {
            let mut seed_builder = <<InnerProductArgPC<G, D> as PolynomialCommitment<G>>::RandomOracle as FiatShamirRng>::Seed::new();
            seed_builder.add_bytes(&Self::PROTOCOL_NAME)?;
            seed_builder.add_bytes(&vk.hash)?;

            // NOTE: We assume the number of accumulators to be clear from the context.
            // As we use constant length encoding of field elements, we may use add_bytes()
            // without producing collisions in the serialization procedure.
            seed_builder.add_bytes(&previous_accumulators)?;
            seed_builder.finalize()
        };
        let mut fs_rng =
            <InnerProductArgPC<G, D> as PolynomialCommitment<G>>::RandomOracle::from_seed(
                fs_rng_init_seed,
            );

        // Sample a new challenge z
        let z = fs_rng.squeeze_128_bits_challenge::<G::ScalarField>();

        let comms_values = previous_accumulators
            .into_par_iter()
            .enumerate()
            .map(|(i, acc)| {
                let final_comm_key = acc.g_final.clone();
                let xi_s = acc.xi_s;

                // Create a LabeledCommitment out of the g_final
                let labeled_comm = {
                    let comm = final_comm_key;

                    LabeledCommitment::new(format!("check_poly_{}", i), comm)
                };

                // Compute the expected value, i.e. the value of the reduction polynomial at z.
                let eval = xi_s.evaluate(z);

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

        fs_rng.absorb(
            &values
                .iter()
                .flat_map(|val| to_bytes!(val).unwrap())
                .collect::<Vec<_>>(),
        );

        // Succinctly verify the dlog opening proof,
        // and get the new reduction polynomial (the new xi's).
        let verifier_state = DomainExtendedPolynomialCommitment::<G, InnerProductArgPC::<G, D>>::succinct_single_point_multi_poly_verify(
            vk, comms.iter(), z, values, &proof.pc_proof, &mut fs_rng
        ).map_err(|e| {
            end_timer!(check_time);
            end_timer!(succinct_time);
            e
        })?;

        end_timer!(check_time);
        end_timer!(succinct_time);

        if verifier_state.is_some() {
            let verifier_state = verifier_state.unwrap();
            Ok(Some(DLogItem::<G> {
                g_final: GroupVec::new(vec![verifier_state.final_comm_key.clone()]),
                xi_s: verifier_state.check_poly.clone(),
            }))
        } else {
            Ok(None)
        }
    }
}

impl<G: Curve, D: Digest + 'static> ItemAccumulator for DLogItemAccumulator<G, D> {
    type AccumulatorProverKey = CommitterKey<G>;
    type AccumulatorVerifierKey = VerifierKey<G>;
    type AccumulationProof = AccumulationProof<G>;
    type Item = DLogItem<G>;

    /// Batch verification of dLog items: combine reduction polynomials and their corresponding G_fins
    /// and perform a single MSM.
    fn check_items<R: RngCore>(
        vk: &Self::AccumulatorVerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let check_time = start_timer!(|| "Check accumulators");

        let final_comm_keys = accumulators
            .iter()
            .flat_map(|acc| acc.g_final.get_vec())
            .collect::<Vec<_>>();
        let xi_s_vec = accumulators
            .iter()
            .map(|acc| acc.xi_s.clone())
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
            .map(|(&chal, xi_s)| {
                Polynomial::from_coefficients_vec(xi_s.compute_scaled_coeffs(-chal))
            })
            .reduce(
                || Polynomial::zero(),
                |acc, scaled_poly| &acc + &scaled_poly,
            );
        end_timer!(batching_time);

        // The dlog "hard part", checking that G_bar = sum_k lambda^k * G_f[k] == Comm(h_bar(X))
        // The equation to check would be:
        // lambda_1 * gfin_1 + ... + lambda_n * gfin_n - combined_h_1 * g_vk_1 - ... - combined_h_m * g_vk_m = 0
        // Where combined_h_i = lambda_1 * h_1_i + ... + lambda_n * h_n_i
        // We do final verification and the batching of the GFin in a single MSM
        let hard_time = start_timer!(|| "Batch verify hard parts");
        let final_val = InnerProductArgPC::<G, D>::inner_commit(
            // The vk might be oversized, but the VariableBaseMSM function, will "trim"
            // the bases in order to be as big as the scalars vector, so no need to explicitly
            // trim the vk here.
            &[G::batch_normalization_into_affine(final_comm_keys).unwrap().as_slice(), vk.comm_key.as_slice()].concat(),
            &[
                batching_chal_pows.as_slice(),
                combined_check_poly.coeffs.as_slice(),
            ]
            .concat(),
            None,
            None,
        )
        .map_err(|e| Error::IncorrectInputLength(e.to_string()))?;
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
        ck: &Self::AccumulatorProverKey,
        accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::AccumulationProof), Error> {
        let accumulate_time = start_timer!(|| "Accumulate");

        // Initialize Fiat-Shamir rng
        let fs_rng_init_seed = {
            let mut seed_builder = <<InnerProductArgPC<G, D> as PolynomialCommitment<G>>::RandomOracle as FiatShamirRng>::Seed::new();
            seed_builder.add_bytes(&Self::PROTOCOL_NAME)?;
            seed_builder.add_bytes(&ck.hash)?;
            // TODO: Shall we decompose this further when passing it to the seed builder ?
            seed_builder.add_bytes(&accumulators)?;
            seed_builder.finalize()
        };
        let mut fs_rng =
            <InnerProductArgPC<G, D> as PolynomialCommitment<G>>::RandomOracle::from_seed(
                fs_rng_init_seed,
            );

        // Sample a new challenge z
        let z = fs_rng.squeeze_128_bits_challenge::<G::ScalarField>();

        // Collect xi_s from the accumulators
        let xi_s = accumulators
            .into_iter()
            .map(|acc| acc.xi_s)
            .collect::<Vec<_>>();

        let poly_time = start_timer!(|| "Open Bullet Polys");

        // Compute multi-poly single-point opening proof for the G_f's, i.e.
        // the commitments of the item polys.
        let opening_proof =
            InnerProductArgPC::<G, D>::open_reduction_polynomials(&ck, xi_s.iter(), z, &mut fs_rng)
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
        vk: &Self::AccumulatorVerifierKey,
        previous_accumulators: Vec<Self::Item>,
        proof: &Self::AccumulationProof,
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
}

/// A composite dlog accumulator/item, comprised of several single dlog items
/// from both groups of the EC cycle.
#[derive(Debug)]
pub struct DualDLogItem<G1: Curve, G2: Curve>(
    pub(crate) Vec<DLogItem<G1>>,
    pub(crate) Vec<DLogItem<G2>>,
);

impl<G1: Curve, G2: Curve> ToBytes for DualDLogItem<G1, G2> {
    fn write<W: Write>(&self, mut writer: W) -> std::io::Result<()> {
        use std::io::{Error, ErrorKind};

        self.0
            .serialize_without_metadata(&mut writer)
            .map_err(|e| Error::new(ErrorKind::Other, format! {"{:?}", e}))?;

        self.1
            .serialize_without_metadata(writer)
            .map_err(|e| Error::new(ErrorKind::Other, format! {"{:?}", e}))
    }
}

pub struct DualDLogItemAccumulator<'a, G1: Curve, G2: Curve, D: Digest> {
    _lifetime: PhantomData<&'a ()>,
    _group_1: PhantomData<G1>,
    _group_2: PhantomData<G2>,
    _digest: PhantomData<D>,
}

// Straight-forward generalization of the dlog item aggregation to DualDLogItem.
impl<'a, G1, G2, D> ItemAccumulator for DualDLogItemAccumulator<'a, G1, G2, D>
where
    G1: Curve<BaseField = <G2 as Group>::ScalarField>,
    G2: Curve<BaseField = <G1 as Group>::ScalarField>,
    D: Digest + 'static,
{
    type AccumulatorProverKey = (&'a CommitterKey<G1>, &'a CommitterKey<G2>);
    type AccumulatorVerifierKey = (&'a VerifierKey<G1>, &'a VerifierKey<G2>);
    type AccumulationProof = (AccumulationProof<G1>, AccumulationProof<G2>);
    type Item = DualDLogItem<G1, G2>;

    fn check_items<R: RngCore>(
        vk: &Self::AccumulatorVerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let g1_accumulators = accumulators
            .iter()
            .flat_map(|acc| acc.0.clone())
            .collect::<Vec<_>>();
        if !DLogItemAccumulator::<G1, D>::check_items::<R>(&vk.0, g1_accumulators.as_slice(), rng)?
        {
            return Ok(false);
        }

        let g2_accumulators = accumulators
            .iter()
            .flat_map(|acc| acc.1.clone())
            .collect::<Vec<_>>();
        if !DLogItemAccumulator::<G2, D>::check_items::<R>(&vk.1, g2_accumulators.as_slice(), rng)?
        {
            return Ok(false);
        }

        Ok(true)
    }

    fn accumulate_items(
        ck: &Self::AccumulatorProverKey,
        accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::AccumulationProof), Error> {
        let g1_accumulators = accumulators
            .iter()
            .flat_map(|acc| acc.0.clone())
            .collect::<Vec<_>>();
        let (_, g1_acc_proof) =
            DLogItemAccumulator::<G1, D>::accumulate_items(&ck.0, g1_accumulators)?;

        let g2_accumulators = accumulators
            .into_iter()
            .flat_map(|acc| acc.1)
            .collect::<Vec<_>>();
        let (_, g2_acc_proof) =
            DLogItemAccumulator::<G2, D>::accumulate_items(&ck.1, g2_accumulators)?;

        let accumulator = DualDLogItem::<G1, G2>(
            vec![DLogItem::<G1>::default()],
            vec![DLogItem::<G2>::default()],
        );
        let accumulation_proof = (g1_acc_proof, g2_acc_proof);

        Ok((accumulator, accumulation_proof))
    }

    fn verify_accumulated_items<R: RngCore>(
        _current_acc: &Self::Item,
        vk: &Self::AccumulatorVerifierKey,
        previous_accumulators: Vec<Self::Item>,
        proof: &Self::AccumulationProof,
        rng: &mut R,
    ) -> Result<bool, Error> {
        let g1_accumulators = previous_accumulators
            .iter()
            .flat_map(|acc| acc.0.clone())
            .collect();
        if !DLogItemAccumulator::<G1, D>::verify_accumulated_items::<R>(
            &DLogItem::<G1>::default(),
            &vk.0,
            g1_accumulators,
            &proof.0,
            rng,
        )? {
            return Ok(false);
        }

        let g2_accumulators = previous_accumulators
            .into_iter()
            .flat_map(|acc| acc.1)
            .collect();
        if !DLogItemAccumulator::<G2, D>::verify_accumulated_items::<R>(
            &DLogItem::<G2>::default(),
            &vk.1,
            g2_accumulators,
            &proof.1,
            rng,
        )? {
            return Ok(false);
        }

        Ok(true)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use poly_commit::{
        ipa_pc::{Parameters, Proof},
        DomainExtendedMultiPointProof, Evaluations, LabeledPolynomial, PCParameters,
        PolynomialCommitment, QuerySet,
    };

    use blake2::Blake2s;
    use digest::Digest;
    use rand::{distributions::Distribution, thread_rng, Rng};
    use std::marker::PhantomData;

    fn get_test_fs_rng<G: Curve, D: Digest + 'static>(
    ) -> <InnerProductArgPC<G, D> as PolynomialCommitment<G>>::RandomOracle {
        let mut seed_builder = <<DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, D>> as PolynomialCommitment<G>>::RandomOracle as FiatShamirRng>::Seed::new();
        seed_builder.add_bytes(b"TEST_SEED").unwrap();
        let fs_rng_seed = seed_builder.finalize();
        <DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, D>> as PolynomialCommitment<
            G,
        >>::RandomOracle::from_seed(fs_rng_seed)
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
    struct VerifierData<'a, G: Curve> {
        vk: VerifierKey<G>,
        comms: Vec<LabeledCommitment<GroupVec<G>>>,
        query_set: QuerySet<'a, G::ScalarField>,
        values: Evaluations<'a, G::ScalarField>,
        proof: DomainExtendedMultiPointProof<G, Proof<G>>,
        polynomials: Vec<LabeledPolynomial<G::ScalarField>>,
        num_polynomials: usize,
        num_points_in_query_set: usize,
        _m: PhantomData<&'a G::ScalarField>, // To avoid compilation issue 'a
    }

    // Samples a random instance of a dlog multi-point multi-poly opening proof according to the
    // specifications in the TestInfo.
    fn get_data_for_verifier<'a, G, D>(
        info: TestInfo,
        pp: Option<Parameters<G>>,
    ) -> Result<VerifierData<'a, G>, Error>
    where
        G: Curve,
        D: Digest + 'static,
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
        let pp = if pp.is_some() {
            pp.unwrap()
        } else {
            DomainExtendedPolynomialCommitment::<G, InnerProductArgPC<G, D>>::setup(max_degree)?
        };

        test_canonical_serialize_deserialize(true, &pp);

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
        let mut labels = Vec::new();
        println!("Sampled supported degree");

        // Generate random dense polynomials
        let num_points_in_query_set =
            rand::distributions::Uniform::from(1..=max_num_queries).sample(rng);
        for i in 0..num_polynomials {
            let label = format!("Test{}", i);
            labels.push(label.clone());
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
            let poly = Polynomial::rand(degree, rng);

            polynomials.push(LabeledPolynomial::new(label, poly, hiding))
        }
        println!("supported degree: {:?}", supported_degree);
        println!("num_points_in_query_set: {:?}", num_points_in_query_set);
        let (ck, vk) = pp.trim(supported_degree)?;
        println!("Trimmed");

        test_canonical_serialize_deserialize(true, &ck);
        test_canonical_serialize_deserialize(true, &vk);

        let (comms, rands) =
            DomainExtendedPolynomialCommitment::<G, InnerProductArgPC<G, D>>::commit_vec(
                &ck,
                &polynomials,
                Some(rng),
            )?;

        // Construct "symmetric" query set: every polynomial is evaluated at every
        // point.
        let mut query_set = QuerySet::new();
        let mut values = Evaluations::new();
        // let mut point = F::one();
        for _ in 0..num_points_in_query_set {
            let point = G::ScalarField::rand(rng);
            for (i, label) in labels.iter().enumerate() {
                query_set.insert((label.clone(), (format!("{}", i), point)));
                let value = polynomials[i].evaluate(point);
                values.insert((label.clone(), point), value);
            }
        }
        println!("Generated query set");

        let mut fs_rng = get_test_fs_rng::<G, D>();
        let proof = DomainExtendedPolynomialCommitment::<G, InnerProductArgPC::<G, D>>::multi_point_multi_poly_open(
            &ck,
            &polynomials,
            &comms,
            &query_set,
            &mut fs_rng,
            &rands,
            Some(rng),
        )?;

        test_canonical_serialize_deserialize(true, &proof);

        Ok(VerifierData {
            vk,
            comms,
            query_set,
            values,
            proof,
            polynomials,
            num_polynomials,
            num_points_in_query_set,
            _m: PhantomData,
        })
    }

    // We sample random instances of multi-point multi-poly dlog opening proofs,
    // produce aggregation proofs for their dlog items and fully verify these aggregation proofs.
    fn accumulation_test<G, D>() -> Result<(), Error>
    where
        G: Curve,
        D: Digest + 'static,
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

        let pp =
            DomainExtendedPolynomialCommitment::<G, InnerProductArgPC<G, D>>::setup(max_degree)?;

        test_canonical_serialize_deserialize(true, &pp);

        let (ck, vk) = pp.trim(max_degree)?;

        test_canonical_serialize_deserialize(true, &ck);
        test_canonical_serialize_deserialize(true, &vk);

        for num_proofs in 1..20 {
            let mut verifier_data_vec = Vec::with_capacity(num_proofs);

            // Generate all proofs and the data needed by the verifier to verify them
            for _ in 0..num_proofs {
                // Modify requirements at random
                info.hiding = rng.gen();
                info.segmented = rng.gen();
                verifier_data_vec
                    .push(get_data_for_verifier::<G, D>(info, Some(pp.clone())).unwrap())
            }

            let mut comms = Vec::new();
            let mut query_sets = Vec::new();
            let mut evals = Vec::new();
            let mut proofs = Vec::new();
            let mut states = Vec::new();

            let state = get_test_fs_rng::<G, D>().get_state().clone();

            verifier_data_vec.iter().for_each(|verifier_data| {
                let len = verifier_data.vk.comm_key.len();
                assert_eq!(&verifier_data.vk.comm_key[..], &vk.comm_key[..len]); // Vk should be equal for all proofs
                comms.push(verifier_data.comms.as_slice());
                query_sets.push(&verifier_data.query_set);
                evals.push(&verifier_data.values);
                proofs.push(&verifier_data.proof);
                states.push(&state);
            });

            // extract the xi's and G_fin's from the proof
            let verifier_state_vec = DomainExtendedPolynomialCommitment::<
                G,
                InnerProductArgPC<G, D>,
            >::batch_succinct_verify(
                &vk,
                comms.clone(),
                query_sets.clone(),
                evals.clone(),
                proofs.clone(),
                states.clone(),
            )?;

            let accumulators = verifier_state_vec
                .into_iter()
                .map(|verifier_state| {
                    let acc = DLogItem::<G> {
                        g_final: GroupVec::new(vec![verifier_state.final_comm_key]),
                        xi_s: verifier_state.check_poly.clone()
                    };
                    test_canonical_serialize_deserialize(true, &acc);
                    acc
                })
                .collect::<Vec<_>>();

            assert!(accumulators.is_valid());

            // provide aggregation proof of the extracted dlog items
            let (_, proof) =
                DLogItemAccumulator::<G, D>::accumulate_items(&ck, accumulators.clone())?;

            test_canonical_serialize_deserialize(true, &proof);

            // Verifier side
            let dummy = DLogItem::<G>::default();
            assert!(DLogItemAccumulator::<G, D>::verify_accumulated_items(
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
    fn batch_verification_test<G, D>() -> Result<(), Error>
    where
        G: Curve,
        D: Digest + 'static,
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

        let pp =
            DomainExtendedPolynomialCommitment::<G, InnerProductArgPC<G, D>>::setup(max_degree)?;
        let (_, vk) = pp.trim(max_degree)?;

        test_canonical_serialize_deserialize(true, &pp);
        test_canonical_serialize_deserialize(true, &vk);

        for num_proofs in 1..20 {
            let mut verifier_data_vec = Vec::with_capacity(num_proofs);

            // Generate all proofs and the data needed by the verifier to verify them
            for _ in 0..num_proofs {
                // Modify requirements at random
                info.hiding = rng.gen();
                info.segmented = rng.gen();
                verifier_data_vec
                    .push(get_data_for_verifier::<G, D>(info, Some(pp.clone())).unwrap())
            }

            let mut comms = Vec::new();
            let mut query_sets = Vec::new();
            let mut evals = Vec::new();
            let mut proofs = Vec::new();
            let mut states = Vec::new();

            let state = get_test_fs_rng::<G, D>().get_state().clone();

            verifier_data_vec.iter().for_each(|verifier_data| {
                let len = verifier_data.vk.comm_key.len();
                assert_eq!(&verifier_data.vk.comm_key[..], &vk.comm_key[..len]); // Vk should be equal for all proofs
                comms.push(verifier_data.comms.as_slice());
                query_sets.push(&verifier_data.query_set);
                evals.push(&verifier_data.values);
                proofs.push(&verifier_data.proof);
                states.push(&state);
            });

            // extract the xi's and G_fin's from the proof
            let verifier_state_vec = DomainExtendedPolynomialCommitment::<
                G,
                InnerProductArgPC<G, D>,
            >::batch_succinct_verify(
                &vk,
                comms.clone(),
                query_sets.clone(),
                evals.clone(),
                proofs.clone(),
                states.clone(),
            )?;

            let accumulators = verifier_state_vec
                .into_iter()
                .map(|verifier_state| {
                    let acc = DLogItem::<G> {
                        g_final: GroupVec::new(vec![verifier_state.final_comm_key]),
                        xi_s: verifier_state.check_poly.clone(),
                    };
                    test_canonical_serialize_deserialize(true, &acc);
                    acc
                })
                .collect::<Vec<_>>();

            assert!(accumulators.is_valid());

            // batch verify the extracted dlog items
            assert!(DLogItemAccumulator::<G, D>::check_items(
                &vk,
                &accumulators,
                rng
            )?);
        }
        Ok(())
    }

    use algebra::curves::tweedle::{dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum};

    #[test]
    fn test_tweedle_accumulate_verify() {
        accumulation_test::<TweedleDee, Blake2s>().unwrap();
        accumulation_test::<TweedleDum, Blake2s>().unwrap();
    }

    #[test]
    fn test_tweedle_batch_verify() {
        batch_verification_test::<TweedleDee, Blake2s>().unwrap();
        batch_verification_test::<TweedleDum, Blake2s>().unwrap();
    }
}
