use crate::darlin::accumulators::to_dual_field_vec::ToDualField;
use crate::darlin::accumulators::{Accumulator, AccumulatorItem, Error};
use algebra::{
    CanonicalDeserialize, CanonicalSerialize, Field, Read, SerializationError, ToConstraintField,
    Write,
};
use derivative::Derivative;
use rand_core::RngCore;
use std::marker::PhantomData;

pub struct CompositeAccumulator<'a, A0: 'a + Accumulator, A1: 'a + Accumulator> {
    _lifetime: PhantomData<&'a ()>,
    acc_0: PhantomData<A0>,
    acc_1: PhantomData<A1>,
}

impl<'a, A0, A1> Accumulator for CompositeAccumulator<'a, A0, A1>
where
    A0: Accumulator,
    A1: Accumulator,
{
    type ProverKey = (&'a A0::ProverKey, &'a A1::ProverKey);
    type VerifierKey = (&'a A0::VerifierKey, &'a A1::VerifierKey);
    type Proof = (A0::Proof, A1::Proof);
    type Item = CompositeAccumulatorItem<A0::Item, A1::Item>;
    type ExpandedItem = (A0::ExpandedItem, A1::ExpandedItem);

    fn expand_item(
        vk: &Self::VerifierKey,
        accumulator: &Self::Item,
    ) -> Result<Self::ExpandedItem, Error> {
        Ok((
            A0::expand_item(&vk.0, &accumulator.0)?,
            A1::expand_item(&vk.1, &accumulator.1)?,
        ))
    }

    fn check_item<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulator: &Self::Item,
        rng: &mut R,
    ) -> Result<Option<Self::ExpandedItem>, Error> {
        let check_0 = A0::check_item(&vk.0, &accumulator.0, rng)?;
        if check_0.is_none() {
            return Ok(None);
        }
        let check_0 = check_0.unwrap();

        let check_1 = A1::check_item(&vk.1, &accumulator.1, rng)?;
        if check_1.is_none() {
            return Ok(None);
        }
        let check_1 = check_1.unwrap();

        Ok(Some((check_0, check_1)))
    }

    fn check_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<Option<Vec<Self::ExpandedItem>>, Error> {
        let acc_0 = accumulators
            .iter()
            .map(|acc| acc.0.clone())
            .collect::<Vec<_>>();
        let check_0 = A0::check_items(&vk.0, &acc_0, rng)?;
        if check_0.is_none() {
            return Ok(None);
        }
        let check_0 = check_0.unwrap();

        let acc_1 = accumulators
            .iter()
            .map(|acc| acc.1.clone())
            .collect::<Vec<_>>();
        let check_1 = A1::check_items(&vk.1, &acc_1, rng)?;
        if check_1.is_none() {
            return Ok(None);
        }
        let check_1 = check_1.unwrap();

        let output = check_0
            .into_iter()
            .zip(check_1.into_iter())
            .map(|(poly_0, poly_1)| (poly_0, poly_1))
            .collect();

        Ok(Some(output))
    }

    fn check_items_optimized<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let acc_0 = accumulators
            .iter()
            .map(|acc| acc.0.clone())
            .collect::<Vec<_>>();
        let check_0 = A0::check_items_optimized(&vk.0, acc_0.as_slice(), rng)?;
        if !check_0 {
            return Ok(false);
        }

        let acc_1 = accumulators
            .iter()
            .map(|acc| acc.1.clone())
            .collect::<Vec<_>>();
        let check_1 = A1::check_items_optimized(&vk.1, acc_1.as_slice(), rng)?;
        if !check_1 {
            return Ok(false);
        }

        return Ok(true);
    }

    fn accumulate_items(
        ck: &Self::ProverKey,
        accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::Proof), Error> {
        let acc_0 = accumulators
            .iter()
            .map(|acc| acc.0.clone())
            .collect::<Vec<_>>();
        let (acc_0_new, proof_0) = A0::accumulate_items(&ck.0, acc_0)?;

        let acc_1 = accumulators
            .iter()
            .map(|acc| acc.1.clone())
            .collect::<Vec<_>>();
        let (acc_1_new, proof_1) = A1::accumulate_items(&ck.1, acc_1)?;

        Ok((
            CompositeAccumulatorItem(acc_0_new, acc_1_new),
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
        let previous_acc_0 = previous_accumulators
            .iter()
            .map(|acc| acc.0.clone())
            .collect::<Vec<_>>();
        let verify_0 = A0::verify_accumulated_items(
            &current_accumulator.0,
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
            .map(|acc| acc.1.clone())
            .collect::<Vec<_>>();
        let verify_1 = A1::verify_accumulated_items(
            &current_accumulator.1,
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
        Ok(CompositeAccumulatorItem(
            A0::trivial_item(&vk.0)?,
            A1::trivial_item(&vk.1)?,
        ))
    }

    fn random_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        Ok(CompositeAccumulatorItem(
            A0::random_item(&vk.0, rng)?,
            A1::random_item(&vk.1, rng)?,
        ))
    }

    fn invalid_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        Ok(CompositeAccumulatorItem(
            A0::invalid_item(&vk.0, rng)?,
            A1::invalid_item(&vk.1, rng)?,
        ))
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct CompositeAccumulatorItem<I0: AccumulatorItem, I1: AccumulatorItem>(pub I0, pub I1);

impl<I0, I1> AccumulatorItem for CompositeAccumulatorItem<I0, I1>
where
    I0: AccumulatorItem,
    I1: AccumulatorItem,
{
}

impl<I0, I1, F> ToConstraintField<F> for CompositeAccumulatorItem<I0, I1>
where
    I0: AccumulatorItem + ToConstraintField<F>,
    I1: AccumulatorItem + ToConstraintField<F>,
    F: Field,
{
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        let mut fes_0 = self.0.to_field_elements()?;
        let mut fes_1 = self.1.to_field_elements()?;
        fes_0.append(&mut fes_1);
        Ok(fes_0)
    }
}

impl<I0, I1, F> ToDualField<F> for CompositeAccumulatorItem<I0, I1>
where
    I0: AccumulatorItem + ToDualField<F>,
    I1: AccumulatorItem + ToDualField<F>,
    F: Field,
{
    fn to_dual_field_elements(&self) -> Result<Vec<F>, Error> {
        let mut fes_0 = self.0.to_dual_field_elements()?;
        let mut fes_1 = self.1.to_dual_field_elements()?;
        fes_0.append(&mut fes_1);
        Ok(fes_0)
    }
}
