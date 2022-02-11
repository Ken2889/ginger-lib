use algebra::{PrimeField, ToConstraintField, Field, EndoMulCurve};
use primitives::{PoseidonSponge, PoseidonParameters, SBox, check_field_equals, AlgebraicSponge};
use crate::Absorbable;

use super::{FiatShamirRng, Error};

/// Circuit implementation of this RNG
pub mod constraints;

impl<SpongeF, P, SB> FiatShamirRng for PoseidonSponge<SpongeF, P, SB>
    where
        SpongeF: PrimeField,
        P: PoseidonParameters<Fr = SpongeF>,
        SB: SBox<Field = SpongeF, Parameters = P>,
{
    type State = Vec<SpongeF>;

    fn from_seed(seed: Vec<u8>) -> Result<Self, Error> {
        // Initialize Poseidon sponge
        let mut sponge = Self::init();

        // Absorb seed elements into the sponge
        let seed_fes: Vec<SpongeF> = seed
            .to_field_elements()
            .map_err(|e| Error::BadFiatShamirInitialization(format!("Unable to convert seed to field elements: {:?}", e)))?;

        seed_fes
            .into_iter()
            .for_each(|fe| <Self as AlgebraicSponge<SpongeF>>::absorb(&mut sponge, fe));

        // If there are pending elements, add them to the state and apply a permutation
        if sponge.pending.len() != 0 {
            sponge.apply_permutation();
        }

        // Return the sponge
        Ok(sponge)
    }

    fn absorb<F: Field, A: Absorbable<F>>(&mut self, to_absorb: A) -> Result<&mut Self, Error> {
        <Self as AlgebraicSponge<SpongeF>>::absorb(self, to_absorb);

        Ok(self)
    }

    fn squeeze_many<F: PrimeField>(&mut self, num: usize) -> Vec<F>
    {
        // We allow only squeezing native field elements
        assert!(check_field_equals::<F, SpongeF>());

        // Squeeze field elements
        let fes = <Self as AlgebraicSponge<SpongeF>>::squeeze(self, num);

        // Cast to SpongeF and return
        unsafe { std::mem::transmute::<Vec<SpongeF>, Vec<F>>(fes) }
    }

    fn squeeze_many_128_bits_challenges<G: EndoMulCurve>(&mut self, num: usize) -> Vec<G::ScalarField> {
        // Squeeze 128 bits from the sponge
        let bits = self.squeeze_bits(num * 128);

        // Return an endo scalar out of them
        bits.chunks(128).flat_map(|bits| G::endo_rep_to_scalar(bits.to_vec())).collect()
    }

    fn get_state(&self) -> Self::State {
        <Self as AlgebraicSponge<SpongeF>>::get_state(self)
    }

    fn set_state(&mut self, new_state: Self::State) {
        <Self as AlgebraicSponge<SpongeF>>::set_state(self, new_state)
    }
}