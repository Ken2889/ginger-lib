use algebra::{PrimeField, ToConstraintField, Field};
use primitives::{PoseidonSponge, PoseidonParameters, SBox, AlgebraicSponge};
use crate::Absorbable;

use super::{FiatShamirRng, Error};
use std::convert::TryInto;

/// Circuit implementation of this RNG
pub mod constraints;
 
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
)]
pub struct PoseidonFSRng<
    SpongeF: PrimeField,
    P: PoseidonParameters<Fr = SpongeF>,
    SB: SBox<Field = SpongeF, Parameters = P>,
> 
{
    sponge: PoseidonSponge<SpongeF, P, SB>,
}

impl<SpongeF, P, SB> FiatShamirRng for PoseidonFSRng<SpongeF, P, SB>
    where
        SpongeF: PrimeField,
        P: PoseidonParameters<Fr = SpongeF>,
        SB: SBox<Field = SpongeF, Parameters = P>,
{
    type State = Vec<SpongeF>;

    fn from_seed(seed: Vec<u8>) -> Result<Self, Error> {
        // Initialize Poseidon sponge
        let mut sponge = PoseidonSponge::<SpongeF, P, SB>::init();

        // Absorb seed elements into the sponge
        let seed_fes: Vec<SpongeF> = seed
            .to_field_elements()
            .map_err(|e| Error::BadFiatShamirInitialization(format!("Unable to convert seed to field elements: {:?}", e)))?;

        PoseidonSponge::<SpongeF, P, SB>::absorb(&mut sponge, seed_fes)
            .map_err(|e| Error::BadFiatShamirInitialization(e.to_string()))?;

        // If there are pending elements, add them to the state and apply a permutation
        if sponge.pending.len() != 0 {
            sponge.apply_permutation();
        }

        // Return the sponge
        Ok(Self { sponge })
    }

    fn absorb<F: Field, A: Absorbable<F>>(&mut self, to_absorb: A) -> Result<&mut Self, Error> {
        self.sponge.absorb(to_absorb)
            .map_err(|e| Error::AbsorptionError(e.to_string()))?;

        Ok(self)
    }

    fn squeeze_many_challenges<const N: usize>(&mut self, num: usize) -> Result<Vec<[bool; N]>, Error> {
        // Squeeze N bits from the sponge
        let bits = self.sponge.squeeze_bits(num * N)
            .map_err(|e| Error::SqueezeError(e.to_string()))?;

        Ok(
            bits
                .chunks_exact(N)
                .map(|bit_chunk| bit_chunk.try_into().unwrap())
                .collect()
        )
    }

    fn get_state(&self) -> Self::State {
        self.sponge.get_state()
    }

    fn set_state(&mut self, new_state: Self::State) {
        self.sponge.set_state(new_state)
    }
}

use algebra::fields::tweedle::Fr as TweedleFr;
use primitives::crh::poseidon::parameters::tweedle_dee::{TweedleFrPoseidonParameters, TweedleFrQuinticSbox};

pub type TweedleFrPoseidonFSRng = PoseidonFSRng<TweedleFr, TweedleFrPoseidonParameters, TweedleFrQuinticSbox>;

use algebra::fields::tweedle::Fq as TweedleFq;
use primitives::crh::poseidon::parameters::tweedle_dum::{TweedleFqPoseidonParameters, TweedleFqQuinticSbox};

pub type TweedleFqPoseidonFSRng = PoseidonFSRng<TweedleFq, TweedleFqPoseidonParameters, TweedleFqQuinticSbox>;