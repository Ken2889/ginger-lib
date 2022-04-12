use crate::darlin::accumulators::to_dual_field_vec::ToDualField;
use crate::darlin::accumulators::{Accumulator, AccumulatorItem, Error};
use algebra::{
    CanonicalDeserialize, CanonicalSerialize, Field, Read, SerializationError, ToConstraintField,
    Write,
};
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
    type ExpandedItem = Vec<A1::ExpandedItem>;

    fn expand_item(
        vk: &Self::VerifierKey,
        accumulator: &Self::Item,
    ) -> Result<Self::ExpandedItem, Error> {
        A1::expand_items(&vk.1, accumulator.non_native.as_slice())
    }

    fn check_item<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulator: &Self::Item,
        rng: &mut R,
    ) -> Result<Option<Self::ExpandedItem>, Error> {
        let check_0 = A0::check_items_optimized(&vk.0, &accumulator.native.as_slice(), rng)?;
        if !check_0 {
            return Ok(None);
        }

        let check_1 = A1::check_items(&vk.1, &accumulator.non_native.as_slice(), rng)?;
        if check_1.is_none() {
            return Ok(None);
        }
        let check_1 = check_1.unwrap();

        Ok(Some(check_1))
    }

    fn check_items<R: RngCore>(
        _vk: &Self::VerifierKey,
        _accumulators: &[Self::Item],
        _rng: &mut R,
    ) -> Result<Option<Vec<Self::ExpandedItem>>, Error> {
        todo!()
    }

    fn check_items_optimized<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let acc_0 = accumulators
            .iter()
            .flat_map(|acc| acc.native.clone())
            .collect::<Vec<_>>();
        let check_0 = A0::check_items_optimized(&vk.0, acc_0.as_slice(), rng)?;
        if !check_0 {
            return Ok(false);
        }

        let acc_1 = accumulators
            .iter()
            .flat_map(|acc| acc.non_native.clone())
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
        Ok(Self::Item {
            native: vec![A0::trivial_item(&vk.0)?],
            non_native: vec![A1::trivial_item(&vk.1)?],
        })
    }

    fn random_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        Ok(Self::Item {
            native: vec![A0::random_item(&vk.0, rng)?],
            non_native: vec![A1::random_item(&vk.1, rng)?],
        })
    }

    fn invalid_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        Ok(Self::Item {
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

impl<I0, I1, F> ToConstraintField<F> for DualAccumulatorItem<I0, I1>
where
    I0: AccumulatorItem + ToConstraintField<F>,
    I1: AccumulatorItem + ToDualField<F>,
    F: Field,
{
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        let mut fes_0 = self.native.to_field_elements()?;
        let mut fes_1 = self.non_native.to_dual_field_elements()?;
        fes_0.append(&mut fes_1);
        Ok(fes_0)
    }
}
