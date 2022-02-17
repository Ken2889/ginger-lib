use std::marker::PhantomData;

use algebra::{Field, PrimeField, ToConstraintField};

use crate::{PoseidonParameters, SBox, SpongeMode, AlgebraicSponge, PoseidonHash, Error};

/// Return true if F1 and F2 are of the same type, false otherwise
pub fn check_field_equals<F1: Field, F2: Field>() -> bool {
    std::any::TypeId::of::<F1>() == std::any::TypeId::of::<F2>()
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = "")
)]
pub struct PoseidonSponge<SpongeF: PrimeField, P: PoseidonParameters<Fr = SpongeF>, SB: SBox<Field = SpongeF, Parameters = P>> {
    pub mode: SpongeMode,
    pub state: Vec<SpongeF>,
    pub pending: Vec<SpongeF>,
    _parameters: PhantomData<P>,
    _sbox: PhantomData<SB>
}

impl<SpongeF, P, SB> PoseidonSponge<SpongeF, P, SB>
    where
        SpongeF: PrimeField,
        P: PoseidonParameters<Fr = SpongeF>,
        SB: SBox<Field = SpongeF, Parameters = P>,
{
    pub fn new(mode: SpongeMode, state: Vec<SpongeF>, pending: Vec<SpongeF>) -> Self {
        Self { mode, state, pending, _parameters: PhantomData, _sbox: PhantomData }
    }

    pub fn apply_permutation(&mut self) {
        for (input, state) in self.pending.iter().zip(self.state.iter_mut()) {
            *state += input;
        }
        PoseidonHash::<SpongeF, P, SB>::poseidon_perm(&mut self.state);
        self.pending.clear();
    }

    fn update(&mut self, input: SpongeF) {
        self.pending.push(input);
        if self.pending.len() == P::R {
            self.apply_permutation();
        }
    }

    fn _absorb(&mut self, elems: Vec<SpongeF>) {
        match self.mode {
            // If we were absorbing keep doing it
            SpongeMode::Absorbing => elems.into_iter().for_each(|f| { self.update(f); }),

            // If we were squeezing, change the mode into absorbing
            SpongeMode::Squeezing => {
                self.mode = SpongeMode::Absorbing;
                self._absorb(elems);
            }
        }
    }

    fn _squeeze(&mut self, num: usize) -> Vec<SpongeF> {
        let mut outputs = Vec::with_capacity(num);

        if num > 0 {
            match self.mode {
                SpongeMode::Absorbing => {
                    // If pending is empty and we were in absorbing, it means that a Poseidon
                    // permutation was applied just before calling squeeze(), (unless you absorbed
                    // nothing, but that is handled) therefore it's wasted to apply another
                    // permutation, and we can directly add state[0] to the outputs
                    // If pending is not empty and we were absorbing, then we need to add the
                    // pending elements to the state and then apply a permutation
                    if !self.pending.is_empty() {
                        self.apply_permutation();
                    }
                    outputs.push(self.state[0].clone());
                    
                    self.mode = SpongeMode::Squeezing;
                    outputs.append(&mut self._squeeze(num - 1));
                },

                // If we were squeezing, then squeeze the required number of field elements
                SpongeMode::Squeezing => {
                    debug_assert!(self.pending.len() == 0);

                    for _ in 0..num {
                        PoseidonHash::<SpongeF, P, SB>::poseidon_perm(&mut self.state);
                        outputs.push(self.state[0].clone());
                    }
                }
            }
        }
        outputs
    }

    pub fn get_pending(&self) -> &[SpongeF] {
        &self.pending
    }
}

impl<SpongeF, P, SB> Default for PoseidonSponge<SpongeF, P, SB>
    where
        SpongeF: PrimeField,
        P: PoseidonParameters<Fr = SpongeF>,
        SB: SBox<Field = SpongeF, Parameters = P>,
{
    fn default() -> Self {
        Self::init()
    }
}

impl<SpongeF, P, SB> AlgebraicSponge<SpongeF> for PoseidonSponge<SpongeF, P, SB>
    where
        SpongeF: PrimeField,
        P: PoseidonParameters<Fr = SpongeF>,
        SB: SBox<Field = SpongeF, Parameters = P>,
{
    type State = Vec<SpongeF>;
    
    fn init() -> Self {
        let mut state = Vec::with_capacity(P::T);
        for i in 0..P::T {
            state.push(P::AFTER_ZERO_PERM[i]);
        }

        Self {
            mode: SpongeMode::Absorbing,
            state,
            pending: Vec::with_capacity(P::R),
            _parameters: PhantomData,
            _sbox: PhantomData,
        }
    }

    fn get_state(&self) -> Vec<SpongeF> {
        self.state.clone()
    }

    fn set_state(&mut self, state: Vec<SpongeF>) {
        assert_eq!(state.len(), P::T);
        self.state = state;
    }

    fn get_mode(&self) -> &SpongeMode {
        &self.mode
    }

    fn set_mode(&mut self, mode: SpongeMode) {
        self.mode = mode;
    }

    fn absorb<F: Field, A: ToConstraintField<F>>(&mut self, to_absorb: A) -> Result<&mut Self, Error>
    {
        // Get F field elements
        let fes = to_absorb.to_field_elements()?;

        if fes.is_empty() {
            Err("Nothing to absorb !")?
        }

        // Convert to_absorb to native field, if needed
        let elems = {

            // We are absorbing an item belonging to native field
            if check_field_equals::<SpongeF, F>() {
                // Safe casting, since we checked that the two types are the same
                // NOTE: If we don't want to use unsafe we can convert by serialization/deserialization
                //       but it's more expensive.
                unsafe { std::mem::transmute::<Vec<F>, Vec<SpongeF>>(fes) }
            } else {
                // We want to absorb items belonging to non native field.
                // Collect all the bits
                let bits = fes
                    .iter()
                    .flat_map(|fe| fe.write_bits())
                    .collect::<Vec<_>>();

                // Read native field elements out of them in F::CAPACITY chunks
                bits.to_field_elements()?
            }
        };

        // Perform absorption
        self._absorb(elems);

        Ok(self)
    }

    fn squeeze(&mut self, num: usize) -> Result<Vec<SpongeF>, Error> {
        if num == 0 {
            Err("Nothing to squeeze !")?
        }

        Ok(self._squeeze(num))
    }
}

#[cfg(test)]
mod test {
    use rand::RngCore;
    use crate::crh::test::algebraic_sponge_consistency_test;
    use super::*;

    // TODO: Is the behavior of this implementation of Sponge consistent with its specifications as crypto primitive ?
    //       Maybe it has to do with definition of state: the whole Sponge state should include also the pending elements
    //       formally.
    fn poseidon_sponge_test<SpongeF, P, SB, R>(rate: usize, rng: &mut R)
    where
        SpongeF: PrimeField,
        P: PoseidonParameters<Fr = SpongeF>,
        SB: SBox<Field = SpongeF, Parameters = P>,
        R: RngCore,
    {
        let mut sponge = PoseidonSponge::<SpongeF, P, SB>::init();
        let mut prev_state = sponge.get_state();

        let fes = (0..rate).map(|_| SpongeF::rand(rng)).collect::<Vec<_>>();

        // Assert that, before absorbing rate elements, state doesn't change.
        sponge.absorb(fes[..rate-1].to_vec()).unwrap();
        assert_eq!(sponge.get_state(), prev_state);
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));
        prev_state = sponge.get_state();

        // After having absorbed rate elements a permutation is triggered and the state changes
        sponge.absorb(fes[rate - 1]).unwrap();
        assert_ne!(sponge.get_state(), prev_state);
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));
        prev_state = sponge.get_state();

        // Assert that, calling squeeze() after absorbing rate elements doesn't change the state.
        sponge.squeeze(1).unwrap();
        assert!(matches!(sponge.get_mode(), SpongeMode::Squeezing));
        assert_eq!(prev_state, sponge.get_state());

        // Assert that the next squeeze() should instead change the state
        sponge.squeeze(1).unwrap();
        assert!(matches!(sponge.get_mode(), SpongeMode::Squeezing));
        assert_ne!(prev_state, sponge.get_state());
    }

    #[cfg(feature = "tweedle")]
    #[test]
    fn test_poseidon_sponge_tweedle_fr() {
        use algebra::{fields::tweedle::{Fr as TweedleFr, Fq as TweedleFq}, BigInteger256};
        use rand::SeedableRng;
        use rand_xorshift::XorShiftRng;
        use crate::{crh::poseidon::parameters::tweedle_dee::*, PoseidonQuinticSBox, FieldBasedHashParameters};

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        algebraic_sponge_consistency_test::<TweedleFrPoseidonSponge, TweedleFr, TweedleFq, _>(
            rng,
            TweedleFr::new(BigInteger256([17557730391780768820, 833391141355621901, 9784327965554015212, 4565399072776154451]))
        );
        poseidon_sponge_test::<TweedleFr, TweedleFrPoseidonParameters, PoseidonQuinticSBox<TweedleFr, TweedleFrPoseidonParameters>, _>(
            TweedleFrPoseidonParameters::R,
            rng,
        );
    }

    #[cfg(feature = "tweedle")]
    #[test]
    fn test_poseidon_sponge_tweedle_fq() {
        use algebra::{fields::tweedle::{Fr as TweedleFr, Fq as TweedleFq}, BigInteger256};
        use rand::SeedableRng;
        use rand_xorshift::XorShiftRng;
        use crate::{crh::poseidon::parameters::tweedle_dum::*, PoseidonQuinticSBox, FieldBasedHashParameters};

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        algebraic_sponge_consistency_test::<TweedleFqPoseidonSponge, TweedleFq, TweedleFr, _>(
            rng,
            TweedleFq::new(BigInteger256([15066118701042310099, 6292950449475163714, 12227215585442390780, 2897043864867774388]))
        );
        poseidon_sponge_test::<TweedleFq, TweedleFqPoseidonParameters, PoseidonQuinticSBox<TweedleFq, TweedleFqPoseidonParameters>, _>(
            TweedleFqPoseidonParameters::R,
            rng,
        );
    }
}