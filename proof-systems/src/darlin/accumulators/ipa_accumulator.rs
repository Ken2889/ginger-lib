use crate::darlin::accumulators::{AccumulatorItem, Error};
use crate::darlin::IPACurve;
use algebra::{CanonicalDeserialize, CanonicalSerialize, DensePolynomial, Group};
use rand_core::RngCore;
use std::fmt::Debug;

pub trait IPAAccumulator {
    type Curve: IPACurve;
    type VerifierKey;
    type Item: IPAAccumulatorItem<Curve = Self::Curve>;

    fn batch_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<
        (
            Self::Curve,
            DensePolynomial<<Self::Curve as Group>::ScalarField>,
        ),
        Error,
    >;
}

pub trait IPAAccumulatorItem: Clone + Debug + CanonicalSerialize + CanonicalDeserialize {
    type Curve: IPACurve;

    fn to_base_field_elements(&self) -> Result<Vec<<Self::Curve as Group>::BaseField>, Error>;
    fn to_scalar_field_elements(&self) -> Result<Vec<<Self::Curve as Group>::ScalarField>, Error>;
}

impl<T: IPAAccumulatorItem> AccumulatorItem for T {}

impl<T> IPAAccumulatorItem for Vec<T>
where
    T: IPAAccumulatorItem,
{
    type Curve = T::Curve;

    fn to_base_field_elements(&self) -> Result<Vec<<Self::Curve as Group>::BaseField>, Error> {
        let mut fes = Vec::with_capacity(self.len());
        for elem in self.iter() {
            fes.append(&mut elem.to_base_field_elements()?);
        }
        Ok(fes)
    }

    fn to_scalar_field_elements(&self) -> Result<Vec<<Self::Curve as Group>::ScalarField>, Error> {
        let mut fes = Vec::with_capacity(self.len());
        for elem in self.iter() {
            fes.append(&mut elem.to_scalar_field_elements()?);
        }
        Ok(fes)
    }
}
