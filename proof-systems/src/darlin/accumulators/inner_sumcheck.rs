use crate::darlin::accumulators::dual::{DualAccumulator, DualAccumulatorItem};
use crate::darlin::accumulators::to_dual_field_vec::ToDualField;
use crate::darlin::accumulators::{Accumulator, AccumulatorItem};
use crate::darlin::accumulators::{BatchResult, BatchableAccumulator};
use crate::darlin::t_dlog_acc_marlin::iop::indexer::Index;
use crate::darlin::{DomainExtendedIpaPc, IPACurve};
use algebra::{
    CanonicalDeserialize, CanonicalSerialize, DensePolynomial, Error, Evaluations, GroupVec,
    PrimeField, Read, SerializationError, ToBits, ToConstraintField, UniformRand, Write,
};
use array_init::array_init;
use bench_utils::{end_timer, start_timer};
use derivative::Derivative;
use fiat_shamir::FiatShamirRng;
use marlin::iop::LagrangeKernel;
use num_traits::{One, Zero};
use poly_commit::ipa_pc::{CommitterKey, InnerProductArgPC};
use poly_commit::{PCKey, PolynomialCommitment};
use rand_core::RngCore;
use rayon::prelude::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
    ParallelSlice,
};
use std::marker::PhantomData;

pub struct InnerSumcheckAccumulator<'a, G, FS> {
    _lifetime: PhantomData<&'a ()>,
    _g: PhantomData<G>,
    _fs: PhantomData<FS>,
}

impl<'a, G, FS> InnerSumcheckAccumulator<'a, G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng,
{
    fn get_segment_size(vk: &<Self as Accumulator>::VerifierKey) -> usize {
        vk.1.degree() + 1
    }
    fn get_num_segments(vk: &<Self as Accumulator>::VerifierKey) -> usize {
        let domain_h = vk.0.index_info.get_domain_h().unwrap();
        let segment_size = Self::get_segment_size(vk);
        let integer_division_with_ceiling =
            |numerator: usize, denominator: usize| (numerator + denominator - 1) / denominator;
        integer_division_with_ceiling(domain_h.size(), segment_size)
    }
}

impl<'a, G, FS> Accumulator for InnerSumcheckAccumulator<'a, G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng,
{
    type ProverKey = ();
    type VerifierKey = <Self as BatchableAccumulator>::VerifierKey;
    type Proof = ();
    type Item = InnerSumcheckItem<G>;

    fn check_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let check_time = start_timer!(|| "Perform batched check of inner-sumcheck accumulators");

        let batch_time = start_timer!(|| "Batch inner-sumcheck accumulators");
        let BatchResult {
            batched_commitment,
            batched_polynomial,
        } = InnerSumcheckAccumulator::<G, FS>::batch_items(vk, accumulators, rng)?;
        end_timer!(batch_time);

        let commit_time = start_timer!(|| "Commit batched inner-sumcheck polynomial");
        let (batched_poly_comm, _) =
            InnerProductArgPC::<G, FS>::commit(&vk.1, &batched_polynomial, false, None).unwrap();
        end_timer!(commit_time);

        end_timer!(check_time);
        Ok(batched_poly_comm == batched_commitment)
    }

    fn accumulate_items(
        _ck: &Self::ProverKey,
        _accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::Proof), Error> {
        unimplemented!()
    }

    fn verify_accumulated_items<R: RngCore>(
        _current_accumulator: &Self::Item,
        _vk: &Self::VerifierKey,
        _previous_accumulators: Vec<Self::Item>,
        _proof: &Self::Proof,
        _rng: &mut R,
    ) -> Result<bool, Error> {
        unimplemented!()
    }

    fn trivial_item(_vk: &Self::VerifierKey) -> Result<Self::Item, Error> {
        let succinct_descriptor = SuccinctInnerSumcheckDescriptor {
            alpha: G::ScalarField::zero(),
            etas: [G::ScalarField::zero(); 3],
        };
        Ok(Self::Item {
            succinct_descriptor,
            c: GroupVec::<G>::zero(),
        })
    }

    fn random_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        let alpha: G::ScalarField = u128::rand(rng).into();
        let etas = array_init(|_| G::ScalarField::rand(rng));
        let succinct_descriptor = SuccinctInnerSumcheckDescriptor { alpha, etas };

        let t_poly = succinct_descriptor.expand(vk.0)?;
        let (c, _) = DomainExtendedIpaPc::<_, FS>::commit(&vk.1, &t_poly, false, None).unwrap();

        Ok(Self::Item {
            succinct_descriptor,
            c,
        })
    }

    fn invalid_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        let alpha: G::ScalarField = u128::rand(rng).into();
        let etas = array_init(|_| G::ScalarField::rand(rng));
        let succinct_descriptor = SuccinctInnerSumcheckDescriptor { alpha, etas };

        let c = (0..Self::get_num_segments(vk))
            .into_iter()
            .map(|_| G::rand(rng))
            .collect();
        let c = GroupVec::new(c);

        Ok(Self::Item {
            succinct_descriptor,
            c,
        })
    }
}

impl<'a, G, FS> BatchableAccumulator for InnerSumcheckAccumulator<'a, G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng,
{
    type Group = G;
    type VerifierKey = (&'a Index<G>, &'a CommitterKey<G>);
    type Item = InnerSumcheckItem<G>;

    fn batch_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<BatchResult<G>, Error> {
        if accumulators.is_empty() {
            return Ok(BatchResult {
                batched_commitment: G::zero(),
                batched_polynomial: DensePolynomial::<G::ScalarField>::zero(),
            });
        }

        let segment_size = Self::get_segment_size(vk);
        let num_segments = Self::get_num_segments(vk);

        let compute_chals_time = start_timer!(|| "Compute batching challenges");
        let mut compute_algebraic_chals = |num_chals: usize| -> Vec<G::ScalarField> {
            let random_scalar = G::ScalarField::rand(rng);
            let mut chal = G::ScalarField::one();
            let mut chals = Vec::with_capacity(num_chals);
            for _ in 0..num_chals {
                chals.push(chal);
                chal *= random_scalar;
            }
            chals
        };

        let chals_for_batching = compute_algebraic_chals(accumulators.len());
        let chals_for_segmentation = compute_algebraic_chals(num_segments);
        end_timer!(compute_chals_time);

        let batch_comm_time = start_timer!(|| "Batch commitments");
        let batched_commitment = accumulators
            .par_iter()
            .zip(chals_for_batching.par_iter())
            .flat_map_iter(|(item, batching_chal)| {
                item.c
                    .into_iter()
                    .zip(chals_for_segmentation.iter())
                    .map(move |(comm, segmentation_chal)| comm * batching_chal * segmentation_chal)
            })
            .reduce(|| G::zero(), |c1, c2| c1 + c2);
        end_timer!(batch_comm_time);

        let batch_accumulator_poly_evals_time =
            start_timer!(|| "Batch domain evaluations of accumulator polys");
        let domain_h = vk.0.index_info.get_domain_h().unwrap();
        let zero_evals = || {
            Evaluations::from_vec_and_domain(
                vec![G::ScalarField::zero(); domain_h.size()],
                domain_h.clone(),
            )
        };

        let batched_t_evals = accumulators
            .into_par_iter()
            .zip(chals_for_batching)
            .map(|(acc, chal)| {
                // instead of expanding the succinct descriptor into the evaluations of the t_poly
                // and then scaling them by chal, we exploit the linearity in eta of the succinct
                // descriptor by scaling the succinct descriptor and then expanding
                let mut scaled_descriptor = acc.succinct_descriptor.clone();
                for eta in scaled_descriptor.etas.iter_mut() {
                    *eta *= chal;
                }
                scaled_descriptor.expand_into_evaluations(vk.0).unwrap()
            })
            .reduce(zero_evals, |a, b| &a + &b);
        end_timer!(batch_accumulator_poly_evals_time);

        let interpolation_time =
            start_timer!(|| "Interpolate batched domain evaluations of accumulator polys");
        let batched_t_poly = batched_t_evals.interpolate();
        end_timer!(interpolation_time);

        let batch_poly_segments_time =
            start_timer!(|| "Batch segments of batched accumulator poly");
        let batched_segmented_t_poly = batched_t_poly
            .par_chunks(segment_size)
            .zip(chals_for_segmentation)
            .map(|(segment, chal)| DensePolynomial::from_coefficients_slice(segment) * &chal)
            .reduce(|| DensePolynomial::zero(), |a, b| a + b);
        end_timer!(batch_poly_segments_time);

        Ok(BatchResult {
            batched_commitment,
            batched_polynomial: batched_segmented_t_poly,
        })
    }
}

/// An item to be collected in an inner-sumcheck accumulator.
#[derive(Derivative)]
#[derivative(Clone, Debug, Eq, PartialEq)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct InnerSumcheckItem<G: IPACurve> {
    /// The succinct descriptor of the accumulator.
    pub succinct_descriptor: SuccinctInnerSumcheckDescriptor<G>,
    /// Commitment of the batched circuit polynomials.
    pub c: GroupVec<G>,
}

#[derive(Derivative)]
#[derivative(Clone, Debug, Eq, PartialEq)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct SuccinctInnerSumcheckDescriptor<G: IPACurve> {
    /// Sampling point.
    pub alpha: G::ScalarField,
    /// Batching randomness.
    pub etas: [G::ScalarField; 3],
}

impl<G: IPACurve> SuccinctInnerSumcheckDescriptor<G> {
    fn expand_into_evaluations(&self, vk: &Index<G>) -> Result<Evaluations<G::ScalarField>, Error> {
        let domain_h = vk.index_info.get_domain_h().unwrap();
        let matrix_a = &vk.a;
        let matrix_b = &vk.b;
        let matrix_c = &vk.c;

        let l_x_alpha_evals = domain_h.domain_eval_lagrange_kernel(self.alpha).unwrap();

        let t_evals = marlin::IOP::calculate_t(
            vec![matrix_a, matrix_b, matrix_c].into_iter(),
            &self.etas,
            domain_h.clone(),
            &l_x_alpha_evals,
        )
        .unwrap();

        Ok(Evaluations::from_vec_and_domain(t_evals, domain_h.clone()))
    }
    pub fn expand(&self, vk: &Index<G>) -> Result<DensePolynomial<G::ScalarField>, Error> {
        let t_evals = self.expand_into_evaluations(vk).unwrap();
        let t_poly = t_evals.interpolate();
        Ok(t_poly)
    }
}

impl<G: IPACurve> ToConstraintField<G::ScalarField> for InnerSumcheckItem<G> {
    fn to_field_elements(&self) -> Result<Vec<G::ScalarField>, Error> {
        let mut fes = Vec::new();

        // The commitment c is over G::BaseField. We serialize it to bits and pack it safely into
        // G::ScalarField elements
        let mut c_g1_bits = Vec::new();
        let c_fes = self.c.to_field_elements()?;
        for fe in c_fes {
            c_g1_bits.append(&mut fe.write_bits());
        }
        fes.append(&mut c_g1_bits.to_field_elements()?);

        // The challenges alpha and eta are already over G::ScalarField. Since only alpha is a
        // 128-bit challenge, we wouldn't save anything from packing the challenges into bits.
        // Therefore we keep them as they are.
        fes.push(self.succinct_descriptor.alpha);
        fes.extend_from_slice(&self.succinct_descriptor.etas);

        Ok(fes)
    }
}

impl<G: IPACurve> ToDualField<G::BaseField> for InnerSumcheckItem<G> {
    fn to_dual_field_elements(&self) -> Result<Vec<G::BaseField>, Error> {
        let mut fes = Vec::new();

        // The commitment c consists of G::BaseField elements only.
        fes.append(&mut self.c.to_field_elements()?);

        // The alpha challenge is a 128 bit element from G::ScalarField. We convert it to bits.
        let mut challenge_bits = Vec::new();
        {
            let to_skip = <G::ScalarField as PrimeField>::size_in_bits() - 128;
            let bits = self.succinct_descriptor.alpha.write_bits();
            challenge_bits.extend_from_slice(&bits[to_skip..]);
        }
        // The eta challenges are 3 generic elements from G::ScalarField. We convert them to bits.
        for fe in self.succinct_descriptor.etas.iter() {
            let bits = fe.write_bits();
            challenge_bits.extend_from_slice(&bits);
        }

        // We pack the full bit vector into native field elements as efficiently as possible (yet
        // still secure).
        fes.append(&mut challenge_bits.to_field_elements()?);

        Ok(fes)
    }
}

impl<G: IPACurve> AccumulatorItem for InnerSumcheckItem<G> {
    type Group = G;
}

pub type DualInnerSumcheckAccumulator<'a, G1, G2, FS> =
    DualAccumulator<'a, InnerSumcheckAccumulator<'a, G1, FS>, InnerSumcheckAccumulator<'a, G2, FS>>;
pub type DualInnerSumcheckItem<G1, G2> =
    DualAccumulatorItem<InnerSumcheckItem<G1>, InnerSumcheckItem<G2>>;

#[cfg(test)]
mod test {
    use super::*;
    use crate::darlin::accumulators::tests::{get_committer_key, get_index, test_check_items};
    use algebra::DualCycle;
    use digest::Digest;
    use rand::thread_rng;

    fn test_inner_sumcheck_check_items<G1, G2, FS, D>(
        pc_max_degree: usize,
        num_constraints: usize,
        num_items: usize,
    ) where
        G1: IPACurve,
        G2: IPACurve,
        G1: DualCycle<G2>,
        FS: FiatShamirRng + 'static,
        D: Digest,
    {
        let rng = &mut thread_rng();
        let pc_vk_g1 = get_committer_key::<G1, FS, D>(pc_max_degree);
        let pc_vk_g2 = get_committer_key::<G2, FS, D>(pc_max_degree);
        let index_g1 = get_index::<G1, G2, _>(num_constraints, rng);
        let index_g2 = get_index::<G2, G1, _>(num_constraints, rng);

        test_check_items::<InnerSumcheckAccumulator<G1, FS>, _>(
            &(&index_g1, &pc_vk_g1),
            num_items,
            rng,
        );

        test_check_items::<DualInnerSumcheckAccumulator<G1, G2, FS>, _>(
            &(&(&index_g1, &pc_vk_g1), &(&index_g2, &pc_vk_g2)),
            num_items,
            rng,
        );
    }

    use algebra::curves::tweedle::{
        dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum,
    };
    use blake2::Blake2s;

    #[cfg(not(feature = "circuit-friendly"))]
    mod chacha_fs {
        use super::*;
        use fiat_shamir::chacha20::FiatShamirChaChaRng;

        #[test]
        fn test_tweedle_inner_sumcheck_check_items() {
            test_inner_sumcheck_check_items::<
                TweedleDee,
                TweedleDum,
                FiatShamirChaChaRng<Blake2s>,
                Blake2s,
            >(127, 1024, 10);
            test_inner_sumcheck_check_items::<
                TweedleDum,
                TweedleDee,
                FiatShamirChaChaRng<Blake2s>,
                Blake2s,
            >(127, 1024, 10);
        }
    }

    #[cfg(feature = "circuit-friendly")]
    mod poseidon_fs {
        use super::*;
        use fiat_shamir::poseidon::{TweedleFqPoseidonFSRng, TweedleFrPoseidonFSRng};

        #[test]
        fn test_tweedle_inner_sumcheck_check_items() {
            test_inner_sumcheck_check_items::<
                TweedleDee,
                TweedleDum,
                TweedleFqPoseidonFSRng,
                Blake2s,
            >(127, 1024, 10);
            test_inner_sumcheck_check_items::<
                TweedleDum,
                TweedleDee,
                TweedleFrPoseidonFSRng,
                Blake2s,
            >(127, 1024, 10);
        }
    }
}
