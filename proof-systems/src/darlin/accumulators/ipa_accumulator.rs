use crate::darlin::accumulators::{AccumulatorItem, Error};
use crate::darlin::IPACurve;
use algebra::{DensePolynomial, Group};
use rand_core::RngCore;

pub trait IPAAccumulator {
    type Group: IPACurve;
    type VerifierKey;
    type Item: AccumulatorItem<Group = Self::Group>;

    fn batch_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<
        (
            Self::Group,
            DensePolynomial<<Self::Group as Group>::ScalarField>,
        ),
        Error,
    >;
}
