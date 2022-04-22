use crate::darlin::accumulators::ipa_accumulator::IPAAccumulatorItem;
use crate::darlin::accumulators::{Accumulator, AccumulatorItem, Error};
use crate::darlin::IPACurve;
use algebra::{
    CanonicalDeserialize, CanonicalSerialize, DualCycle, Read, SerializationError,
    ToConstraintField, Write,
};
use bench_utils::{end_timer, start_timer};
use derivative::Derivative;
use rand_core::RngCore;
use std::marker::PhantomData;

pub struct DualAccumulator<'a, A0, A1> {
    _lifetime: PhantomData<&'a ()>,
    acc_0: PhantomData<A0>,
    acc_1: PhantomData<A1>,
}

impl<'a, A0, A1> Accumulator for DualAccumulator<'a, A0, A1>
where
    A0: 'a + Accumulator,
    A1: 'a + Accumulator,
{
    type ProverKey = (&'a A0::ProverKey, &'a A1::ProverKey);
    type VerifierKey = (&'a A0::VerifierKey, &'a A1::VerifierKey);
    type Proof = (A0::Proof, A1::Proof);
    type Item = DualAccumulatorItem<A0::Item, A1::Item>;

    fn check_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[DualAccumulatorItem<A0::Item, A1::Item>],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let check_time = start_timer!(|| "Check dual accumulators");

        let check_native_time = start_timer!(|| "Check native part of accumulators");
        let acc_0 = accumulators
            .iter()
            .flat_map(|acc| acc.native.clone())
            .collect::<Vec<_>>();
        let check_0 = A0::check_items(&vk.0, acc_0.as_slice(), rng)?;
        if !check_0 {
            return Ok(false);
        }
        end_timer!(check_native_time);

        let check_non_native_time = start_timer!(|| "Check non-native part of accumulators");
        let acc_1 = accumulators
            .iter()
            .flat_map(|acc| acc.non_native.clone())
            .collect::<Vec<_>>();
        let check_1 = A1::check_items(&vk.1, acc_1.as_slice(), rng)?;
        if !check_1 {
            return Ok(false);
        }
        end_timer!(check_non_native_time);

        end_timer!(check_time);
        return Ok(true);
    }

    fn accumulate_items(
        ck: &Self::ProverKey,
        accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::Proof), Error> {
        let acc_0 = accumulators
            .iter()
            .flat_map(|acc| acc.native.clone())
            .collect::<Vec<_>>();
        let (acc_0_new, proof_0) = A0::accumulate_items(&ck.0, acc_0)?;

        let acc_1 = accumulators
            .iter()
            .flat_map(|acc| acc.non_native.clone())
            .collect::<Vec<_>>();
        let (acc_1_new, proof_1) = A1::accumulate_items(&ck.1, acc_1)?;

        Ok((
            Self::Item {
                native: vec![acc_0_new],
                non_native: vec![acc_1_new],
            },
            (proof_0, proof_1),
        ))
    }

    fn verify_accumulated_items<R: RngCore>(
        current_accumulator: &Self::Item,
        vk: &Self::VerifierKey,
        previous_accumulators: Vec<Self::Item>,
        proof: &Self::Proof,
        rng: &mut R,
    ) -> Result<bool, Error> {
        assert!(current_accumulator.native.len() != 1 || current_accumulator.non_native.len() != 1);
        let previous_acc_0 = previous_accumulators
            .iter()
            .flat_map(|acc| acc.native.clone())
            .collect::<Vec<_>>();
        let verify_0 = A0::verify_accumulated_items(
            &current_accumulator.native[0],
            &vk.0,
            previous_acc_0,
            &proof.0,
            rng,
        )?;
        if !verify_0 {
            return Ok(false);
        }

        let previous_acc_1 = previous_accumulators
            .iter()
            .flat_map(|acc| acc.non_native.clone())
            .collect::<Vec<_>>();
        let verify_1 = A1::verify_accumulated_items(
            &current_accumulator.non_native[0],
            &vk.1,
            previous_acc_1,
            &proof.1,
            rng,
        )?;
        if !verify_1 {
            return Ok(false);
        }

        Ok(true)
    }

    fn trivial_item(vk: &Self::VerifierKey) -> Result<Self::Item, Error> {
        Ok(DualAccumulatorItem {
            native: vec![A0::trivial_item(&vk.0)?],
            non_native: vec![A1::trivial_item(&vk.1)?],
        })
    }

    fn random_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        Ok(DualAccumulatorItem {
            native: vec![A0::random_item(&vk.0, rng)?],
            non_native: vec![A1::random_item(&vk.1, rng)?],
        })
    }

    fn invalid_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        Ok(DualAccumulatorItem {
            native: vec![A0::invalid_item(&vk.0, rng)?],
            non_native: vec![A1::invalid_item(&vk.1, rng)?],
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct DualAccumulatorItem<I0, I1>
where
    I0: AccumulatorItem,
    I1: AccumulatorItem,
{
    pub native: Vec<I0>,
    pub non_native: Vec<I1>,
}

impl<I0, I1> AccumulatorItem for DualAccumulatorItem<I0, I1>
where
    I0: AccumulatorItem,
    I1: AccumulatorItem,
{
}

impl<G0, G1, I0, I1> ToConstraintField<G0::ScalarField> for DualAccumulatorItem<I0, I1>
where
    G0: IPACurve,
    G1: IPACurve,
    G0: DualCycle<G1>,
    I0: IPAAccumulatorItem<Curve = G0>,
    I1: IPAAccumulatorItem<Curve = G1>,
{
    fn to_field_elements(&self) -> Result<Vec<G0::ScalarField>, Error> {
        let mut fes_0 = self.native.to_scalar_field_elements()?;
        let mut fes_1 = self.non_native.to_base_field_elements()?;
        fes_0.append(&mut fes_1);
        Ok(fes_0)
    }
}
