use crate::darlin::accumulators::dlog::DLogAccumulator;
use crate::darlin::accumulators::dual::{DualAccumulator, DualAccumulatorItem};
use crate::darlin::accumulators::inner_sumcheck::{InnerSumcheckAccumulator, InnerSumcheckItem};
use crate::darlin::accumulators::to_dual_field_vec::ToDualField;
use crate::darlin::accumulators::SingleSegmentBatchingResult;
use crate::darlin::accumulators::{Accumulator, AccumulatorItem, Error};
use crate::darlin::t_dlog_acc_marlin::iop::indexer::Index;
use crate::darlin::IPACurve;
use algebra::serialize::*;
use algebra::{ToConstraintField, UniformRand};
use bench_utils::{end_timer, start_timer};
use derivative::Derivative;
use fiat_shamir::FiatShamirRng;
use poly_commit::ipa_pc::{CommitterKey, DLogItem, InnerProductArgPC};
use poly_commit::PolynomialCommitment;
use rand_core::RngCore;
use std::marker::PhantomData;

pub struct TDLogAccumulator<'a, G, FS> {
    _lifetime: PhantomData<&'a ()>,
    _g: PhantomData<G>,
    _fs: PhantomData<FS>,
}

impl<'a, G, FS> Accumulator for TDLogAccumulator<'a, G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng + 'static,
{
    type ProverKey = ();
    type VerifierKey = (&'a Index<G>, &'a CommitterKey<G>);
    type Proof = ();
    type Item = TDLogItem<G>;
    type BatchingResult = SingleSegmentBatchingResult<G>;

    fn batch_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<Self::BatchingResult, Error> {
        let (t_accs, dlog_accs): (Vec<_>, Vec<_>) = accumulators
            .iter()
            .map(|acc| (acc.t_item.clone(), acc.dlog_item.clone()))
            .unzip();

        let batch_t_acc_time = start_timer!(|| "Batch t accumulator");
        let SingleSegmentBatchingResult {
            batched_commitment: batched_t_comm,
            batched_polynomial: batched_t_poly,
        } = InnerSumcheckAccumulator::<G, FS>::batch_items(vk, t_accs.as_slice(), rng)?;
        end_timer!(batch_t_acc_time);

        let batch_dlog_acc_time = start_timer!(|| "Batch dlog accumulator");
        let SingleSegmentBatchingResult {
            batched_commitment: batched_dlog_comm,
            batched_polynomial: batched_dlog_poly,
        } = DLogAccumulator::<G, FS>::batch_items(&vk.1, dlog_accs.as_slice(), rng)?;
        end_timer!(batch_dlog_acc_time);

        let batch_t_and_dlog_time =
            start_timer!(|| "Batch together already batched t and dlog accumulators");
        let batching_chal = G::ScalarField::rand(rng);
        let batched_commitment = batched_t_comm + batched_dlog_comm * &batching_chal;
        let batched_polynomial = batched_t_poly + batched_dlog_poly * &batching_chal;
        end_timer!(batch_t_and_dlog_time);

        Ok(SingleSegmentBatchingResult {
            batched_commitment,
            batched_polynomial,
        })
    }

    fn check_batched_items(
        vk: &Self::VerifierKey,
        batching_result: &Self::BatchingResult,
    ) -> Result<bool, Error> {
        let commit_time = start_timer!(|| "Commit batched dlog polynomial");

        let (batched_poly_comm, _) = InnerProductArgPC::<G, FS>::commit(
            vk.1,
            &batching_result.batched_polynomial,
            false,
            None,
        )
        .unwrap();

        end_timer!(commit_time);

        Ok(batched_poly_comm == batching_result.batched_commitment)
    }

    fn check_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let check_time = start_timer!(|| "Perform batched check of t-dlog accumulators");

        let batch_time = start_timer!(|| "Batch t-dlog accumulators");
        let SingleSegmentBatchingResult {
            batched_commitment,
            batched_polynomial,
        } = Self::batch_items(vk, accumulators, rng)?;
        end_timer!(batch_time);

        let commit_time = start_timer!(|| "Commit batched t-dlog polynomial");
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

    fn trivial_item(vk: &Self::VerifierKey) -> Result<Self::Item, Error> {
        Ok(Self::Item {
            t_item: InnerSumcheckAccumulator::<G, FS>::trivial_item(vk)?,
            dlog_item: DLogAccumulator::<G, FS>::trivial_item(vk.1)?,
        })
    }

    fn random_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        Ok(Self::Item {
            t_item: InnerSumcheckAccumulator::<G, FS>::random_item(vk, rng)?,
            dlog_item: DLogAccumulator::<G, FS>::random_item(vk.1, rng)?,
        })
    }

    fn invalid_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        Ok(Self::Item {
            t_item: InnerSumcheckAccumulator::<G, FS>::invalid_item(vk, rng)?,
            dlog_item: DLogAccumulator::<G, FS>::invalid_item(vk.1, rng)?,
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct TDLogItem<G: IPACurve> {
    pub t_item: InnerSumcheckItem<G>,
    pub dlog_item: DLogItem<G>,
}

impl<G: IPACurve> ToConstraintField<G::ScalarField> for TDLogItem<G> {
    fn to_field_elements(&self) -> Result<Vec<G::ScalarField>, Error> {
        let mut fes_0 = self.t_item.to_field_elements()?;
        let mut fes_1 = self.dlog_item.to_field_elements()?;
        fes_0.append(&mut fes_1);
        Ok(fes_0)
    }
}

impl<G: IPACurve> ToDualField<G::BaseField> for TDLogItem<G> {
    fn to_dual_field_elements(&self) -> Result<Vec<G::BaseField>, Error> {
        let mut fes_0 = self.t_item.to_dual_field_elements()?;
        let mut fes_1 = self.dlog_item.to_dual_field_elements()?;
        fes_0.append(&mut fes_1);
        Ok(fes_0)
    }
}

impl<G: IPACurve> AccumulatorItem for TDLogItem<G> {
    type Curve = G;
}

pub type DualTDLogAccumulator<'a, G1, G2, FS> =
    DualAccumulator<'a, TDLogAccumulator<'a, G1, FS>, TDLogAccumulator<'a, G2, FS>>;
pub type DualTDLogItem<G1, G2> = DualAccumulatorItem<TDLogItem<G1>, TDLogItem<G2>>;

#[cfg(test)]
mod test {
    use super::*;
    use crate::darlin::accumulators::tests::{get_committer_key, get_index, test_check_items};
    use algebra::DualCycle;
    use digest::Digest;
    use rand::thread_rng;

    fn test_t_dlog_check_items<G1, G2, FS, D>(
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

        test_check_items::<TDLogAccumulator<G1, FS>, _>(&(&index_g1, &pc_vk_g1), num_items, rng);

        test_check_items::<DualTDLogAccumulator<G1, G2, FS>, _>(
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
        fn test_tweedle_t_dlog_check_items() {
            test_t_dlog_check_items::<TweedleDee, TweedleDum, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                127, 1024, 10,
            );
            test_t_dlog_check_items::<TweedleDum, TweedleDee, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                127, 1024, 10,
            );
        }
    }

    #[cfg(feature = "circuit-friendly")]
    mod poseidon_fs {
        use super::*;
        use fiat_shamir::poseidon::{TweedleFqPoseidonFSRng, TweedleFrPoseidonFSRng};

        #[test]
        fn test_tweedle_t_dlog_check_items() {
            test_t_dlog_check_items::<TweedleDee, TweedleDum, TweedleFqPoseidonFSRng, Blake2s>(
                127, 1024, 10,
            );
            test_t_dlog_check_items::<TweedleDum, TweedleDee, TweedleFrPoseidonFSRng, Blake2s>(
                127, 1024, 10,
            );
        }
    }
}
