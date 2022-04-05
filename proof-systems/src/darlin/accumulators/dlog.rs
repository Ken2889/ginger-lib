//! Halo's amortization strategy for the hard parts of the dlog/IPA commitment scheme
//! as separate public aggregation/accumulation scheme according to [BCMS20](https://eprint.iacr.org/2020/499).
//! The hard part consists of checking that the final committer key G_f (after all the
//! reduction steps) is the polynomial commitment of the succinct 'reduction polynomial'
//!     h(X) = (1 + xi_d * X^1)*(1 + xi_{d-1} * X^2) * ... (1 + xi_{1}*X^{2^d}),
//! where the xi_1,...,xi_d are the challenges of the dlog reduction.
use crate::darlin::{
    accumulators::{AccumulationProof, ItemAccumulator},
    DomainExtendedIpaPc,
};
use algebra::polynomial::DensePolynomial as Polynomial;
use algebra::{
    serialize::*, DensePolynomial, Group, GroupVec, PrimeField, ToBits, ToConstraintField,
    UniformRand,
};
use bench_utils::*;
use fiat_shamir::{FiatShamirRng, FiatShamirRngSeed};
use num_traits::{One, Zero};
pub use poly_commit::ipa_pc::DLogItem;
use poly_commit::ipa_pc::LabeledSuccinctCheckPolynomial;
use poly_commit::{
    ipa_pc::{CommitterKey, IPACurve, InnerProductArgPC, VerifierKey},
    Error as PCError, LabeledCommitment, PolynomialCommitment,
};
use rand::RngCore;
use rayon::prelude::*;
use std::marker::PhantomData;

pub struct DLogItemAccumulator<G: IPACurve, FS: FiatShamirRng + 'static> {
    _group: PhantomData<G>,
    _fs_rng: PhantomData<FS>,
}

impl<G: IPACurve, FS: FiatShamirRng + 'static> DLogItemAccumulator<G, FS> {
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
    ) -> Result<Option<DLogItem<G>>, PCError> {
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

impl<G: IPACurve, FS: FiatShamirRng + 'static> ItemAccumulator for DLogItemAccumulator<G, FS> {
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
    ) -> Result<bool, PCError> {
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
                Polynomial::from_coefficients_vec(check_poly.compute_scaled_coeffs(-chal))
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
        ck: &Self::AccumulatorProverKey,
        accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::AccumulationProof), PCError> {
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
        vk: &Self::AccumulatorVerifierKey,
        previous_accumulators: Vec<Self::Item>,
        proof: &Self::AccumulationProof,
        rng: &mut R,
    ) -> Result<bool, PCError> {
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
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DualDLogItem<G1: IPACurve, G2: IPACurve>(
    pub(crate) Vec<DLogItem<G1>>,
    pub(crate) Vec<DLogItem<G2>>,
);

impl<G1: IPACurve, G2: IPACurve> DualDLogItem<G1, G2> {
    /// Generate a random (but valid)  instance of `DualDLogItem`, for test purposes only.
    pub fn generate_random<R: RngCore, FS: FiatShamirRng>(
        rng: &mut R,
        committer_key_g1: &CommitterKey<G1>,
        committer_key_g2: &CommitterKey<G2>,
    ) -> Self {
        Self(
            vec![DLogItem::generate_random::<R, FS>(rng, committer_key_g1)],
            vec![DLogItem::generate_random::<R, FS>(rng, committer_key_g2)],
        )
    }

    /// Generate a random invalid instance of `DualDLogItem`, for test purposes only.
    /// The "left" accumulator (`self.0`) is invalid, while the "right" one (`self.1`) is valid.
    pub fn generate_invalid_left<R: RngCore, FS: FiatShamirRng>(
        rng: &mut R,
        committer_key_g1: &CommitterKey<G1>,
        committer_key_g2: &CommitterKey<G2>,
    ) -> Self {
        Self(
            vec![DLogItem::generate_invalid::<R, FS>(rng, committer_key_g1)],
            vec![DLogItem::generate_random::<R, FS>(rng, committer_key_g2)],
        )
    }

    /// Generate a random invalid instance of `DualDLogItem`, for test purposes only.
    /// The "left" accumulator (`self.0`) is valid, while the "right" one (`self.1`) is invalid.
    pub fn generate_invalid_right<R: RngCore, FS: FiatShamirRng>(
        rng: &mut R,
        committer_key_g1: &CommitterKey<G1>,
        committer_key_g2: &CommitterKey<G2>,
    ) -> Self {
        Self(
            vec![DLogItem::generate_random::<R, FS>(rng, committer_key_g1)],
            vec![DLogItem::generate_invalid::<R, FS>(rng, committer_key_g2)],
        )
    }

    /// Generate a random invalid instance of `DualDLogItem`, for test purposes only.
    /// Both accumulators are invalid.
    pub fn generate_invalid<R: RngCore, FS: FiatShamirRng>(
        rng: &mut R,
        committer_key_g1: &CommitterKey<G1>,
        committer_key_g2: &CommitterKey<G2>,
    ) -> Self {
        Self(
            vec![DLogItem::generate_invalid::<R, FS>(rng, committer_key_g1)],
            vec![DLogItem::generate_invalid::<R, FS>(rng, committer_key_g2)],
        )
    }

    /// Generate the trivial `DualDLogItem`.
    pub fn generate_trivial<FS: FiatShamirRng>(
        committer_key_g1: &CommitterKey<G1>,
        committer_key_g2: &CommitterKey<G2>,
    ) -> Self {
        Self(
            vec![DLogItem::<G1>::generate_trivial(committer_key_g1)],
            vec![DLogItem::<G2>::generate_trivial(committer_key_g2)],
        )
    }

    /// Compute the polynomial associated to the accumulator.
    pub fn compute_poly(
        &self,
    ) -> (
        Vec<DensePolynomial<G1::ScalarField>>,
        Vec<DensePolynomial<G2::ScalarField>>,
    ) {
        (
            self.0
                .iter()
                .map(|el| DensePolynomial::from_coefficients_vec(el.check_poly.compute_coeffs()))
                .collect(),
            self.1
                .iter()
                .map(|el| DensePolynomial::from_coefficients_vec(el.check_poly.compute_coeffs()))
                .collect(),
        )
    }
}

impl<G1, G2> ToConstraintField<G1::ScalarField> for DualDLogItem<G2, G1>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
{
    /// Conversion of the MarlinDeferredData to circuit inputs, which are elements
    /// over G1::ScalarField.
    fn to_field_elements(&self) -> Result<Vec<G1::ScalarField>, Box<dyn std::error::Error>> {
        assert!(self.0.len() == 1 && self.1.len() == 1);
        let to_skip = <G1::ScalarField as PrimeField>::size_in_bits() - 128;
        let mut fes = Vec::new();

        // Convert previous_acc into G1::ScalarField field elements (the circuit field,
        // called native in the sequel)

        // The final_comm_key of the previous node consists of native field elements only
        let final_comm_key_g2 = self.0[0].final_comm_key.clone();
        fes.append(&mut final_comm_key_g2.to_field_elements()?);

        // Convert check_poly, which are 128 bit elements from G2::ScalarField, to the native field.
        // We packing the full bit vector into native field elements as efficient as possible (yet
        // still secure).
        let mut check_poly_bits = Vec::new();
        for fe in self.0[0].check_poly.chals.iter() {
            let bits = fe.write_bits();
            // write_bits() outputs a Big Endian bit order representation of fe and the same
            // expects [bool].to_field_elements(): therefore we need to take the last 128 bits,
            // e.g. we need to skip the first MODULUS_BITS - 128 bits.
            debug_assert!(
                <[bool] as ToConstraintField<G2::ScalarField>>::to_field_elements(&bits[to_skip..])
                    .unwrap()[0]
                    == *fe
            );
            check_poly_bits.extend_from_slice(&bits[to_skip..]);
        }
        fes.append(&mut check_poly_bits.to_field_elements()?);

        // Convert the pre-previous acc into native field elements.

        // The final_comm_key of the pre-previous node is in G1, hence over G2::ScalarField.
        // We serialize them all to bits and pack them safely into native field elements
        let final_comm_key_g1 = self.1[0].final_comm_key.clone();
        let mut final_comm_key_g1_bits = Vec::new();
        let c_fes = final_comm_key_g1.to_field_elements()?;
        for fe in c_fes {
            final_comm_key_g1_bits.append(&mut fe.write_bits());
        }
        fes.append(&mut final_comm_key_g1_bits.to_field_elements()?);

        // Although the xi's of the pre-previous node are by default 128 bit elements from G1::ScalarField
        // (we do field arithmetics with them lateron) we do not want waste space.
        // As for the xi's of the previous node, we serialize them all to bits and pack them into native
        // field elements as efficient as possible (yet secure).
        let mut check_poly_bits = Vec::new();
        for fe in self.1[0].check_poly.chals.iter() {
            let bits = fe.write_bits();
            // write_bits() outputs a Big Endian bit order representation of fe and the same
            // expects [bool].to_field_elements(): therefore we need to take the last 128 bits,
            // e.g. we need to skip the first MODULUS_BITS - 128 bits.
            debug_assert!(
                <[bool] as ToConstraintField<G1::ScalarField>>::to_field_elements(&bits[to_skip..])
                    .unwrap()[0]
                    == *fe
            );
            check_poly_bits.extend_from_slice(&bits[to_skip..]);
        }
        fes.append(&mut check_poly_bits.to_field_elements()?);

        Ok(fes)
    }
}

pub struct DualDLogItemAccumulator<'a, G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> {
    _lifetime: PhantomData<&'a ()>,
    _group_1: PhantomData<G1>,
    _group_2: PhantomData<G2>,
    _fs_rng: PhantomData<FS>,
}

// Straight-forward generalization of the dlog item aggregation to DualDLogItem.
impl<'a, G1, G2, FS> ItemAccumulator for DualDLogItemAccumulator<'a, G1, G2, FS>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>,
    FS: FiatShamirRng + 'static,
{
    type AccumulatorProverKey = (&'a CommitterKey<G1>, &'a CommitterKey<G2>);
    type AccumulatorVerifierKey = (&'a VerifierKey<G1>, &'a VerifierKey<G2>);
    type AccumulationProof = (AccumulationProof<G1>, AccumulationProof<G2>);
    type Item = DualDLogItem<G1, G2>;

    fn check_items<R: RngCore>(
        vk: &Self::AccumulatorVerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, PCError> {
        let g1_accumulators = accumulators
            .iter()
            .flat_map(|acc| acc.0.clone())
            .collect::<Vec<_>>();
        if !DLogItemAccumulator::<G1, FS>::check_items::<R>(&vk.0, g1_accumulators.as_slice(), rng)?
        {
            return Ok(false);
        }

        let g2_accumulators = accumulators
            .iter()
            .flat_map(|acc| acc.1.clone())
            .collect::<Vec<_>>();
        if !DLogItemAccumulator::<G2, FS>::check_items::<R>(&vk.1, g2_accumulators.as_slice(), rng)?
        {
            return Ok(false);
        }

        Ok(true)
    }

    fn accumulate_items(
        ck: &Self::AccumulatorProverKey,
        accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::AccumulationProof), PCError> {
        let g1_accumulators = accumulators
            .iter()
            .flat_map(|acc| acc.0.clone())
            .collect::<Vec<_>>();
        let (_, g1_acc_proof) =
            DLogItemAccumulator::<G1, FS>::accumulate_items(&ck.0, g1_accumulators)?;

        let g2_accumulators = accumulators
            .into_iter()
            .flat_map(|acc| acc.1)
            .collect::<Vec<_>>();
        let (_, g2_acc_proof) =
            DLogItemAccumulator::<G2, FS>::accumulate_items(&ck.1, g2_accumulators)?;

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
    ) -> Result<bool, PCError> {
        let g1_accumulators = previous_accumulators
            .iter()
            .flat_map(|acc| acc.0.clone())
            .collect();
        if !DLogItemAccumulator::<G1, FS>::verify_accumulated_items::<R>(
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
        if !DLogItemAccumulator::<G2, FS>::verify_accumulated_items::<R>(
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
    use algebra::SemanticallyValid;
    use blake2::Blake2s;
    use derivative::Derivative;
    use digest::Digest;
    use poly_commit::{
        ipa_pc::Proof, DomainExtendedMultiPointProof, DomainExtendedPolynomialCommitment, Error,
        Evaluations, LabeledPolynomial, PCKey, PolynomialCommitment, QueryMap,
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
    ) -> Result<VerifierData<'a, G>, PCError>
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
            let poly = Polynomial::rand(degree, rng);

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
    fn accumulation_test<G, D, FS>() -> Result<(), PCError>
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
            let (_, proof) =
                DLogItemAccumulator::<G, FS>::accumulate_items(&vk, accumulators.clone())?;

            test_canonical_serialize_deserialize(true, &proof);

            // Verifier side
            let dummy = DLogItem::<G>::default();
            assert!(DLogItemAccumulator::<G, FS>::verify_accumulated_items(
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
    fn batch_verification_test<G, D, FS>() -> Result<(), PCError>
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
            assert!(DLogItemAccumulator::<G, FS>::check_items(
                &vk,
                &accumulators,
                rng
            )?);
        }
        Ok(())
    }

    fn random_accumulator_test<G, D, FS>() -> Result<(), Error>
    where
        G: IPACurve,
        D: Digest + 'static,
        FS: FiatShamirRng + 'static,
    {
        let rng = &mut thread_rng();

        let max_degree = rand::distributions::Uniform::from(2..=128);
        let num_samples = 10;

        for _ in 0..num_samples {
            let max_degree = rng.sample(max_degree);
            let (ck, vk) =
                DomainExtendedPolynomialCommitment::<G, InnerProductArgPC<G, FS>>::setup::<D>(
                    max_degree,
                )?;
            let dlog_item = DLogItem::generate_random::<_, FS>(rng, &ck);
            let res = DLogItemAccumulator::<_, FS>::check_items(&vk, &[dlog_item], rng)?;

            assert!(res);
        }

        Ok(())
    }

    fn trivial_accumulator_test<G, D, FS>() -> Result<(), Error>
    where
        G: IPACurve,
        D: Digest + 'static,
        FS: FiatShamirRng + 'static,
    {
        let rng = &mut thread_rng();

        let max_degree = rand::distributions::Uniform::from(2..=128);
        let num_samples = 10;

        for _ in 0..num_samples {
            let max_degree = rng.sample(max_degree);
            let (ck, vk) =
                DomainExtendedPolynomialCommitment::<G, InnerProductArgPC<G, FS>>::setup::<D>(
                    max_degree,
                )?;
            let dlog_item = DLogItem::generate_trivial(&ck);
            let res = DLogItemAccumulator::<_, FS>::check_items(&vk, &[dlog_item], rng)?;

            assert!(res);
        }

        Ok(())
    }

    use algebra::curves::tweedle::{
        dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum,
    };

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
        fn test_tweedle_random_accumulator() {
            random_accumulator_test::<TweedleDee, Blake2s, FiatShamirChaChaRng<Blake2s>>().unwrap();
            random_accumulator_test::<TweedleDum, Blake2s, FiatShamirChaChaRng<Blake2s>>().unwrap();
        }

        #[test]
        fn test_tweedle_trivial_accumulator() {
            trivial_accumulator_test::<TweedleDee, Blake2s, FiatShamirChaChaRng<Blake2s>>()
                .unwrap();
            trivial_accumulator_test::<TweedleDum, Blake2s, FiatShamirChaChaRng<Blake2s>>()
                .unwrap();
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
        fn test_tweedle_random_accumulator() {
            random_accumulator_test::<TweedleDee, Blake2s, TweedleFqPoseidonFSRng>().unwrap();
            random_accumulator_test::<TweedleDum, Blake2s, TweedleFrPoseidonFSRng>().unwrap();
        }

        #[test]
        fn test_tweedle_trivial_accumulator() {
            trivial_accumulator_test::<TweedleDee, Blake2s, TweedleFqPoseidonFSRng>().unwrap();
            trivial_accumulator_test::<TweedleDum, Blake2s, TweedleFrPoseidonFSRng>().unwrap();
        }
    }
}
