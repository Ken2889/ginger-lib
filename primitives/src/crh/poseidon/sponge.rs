use std::marker::PhantomData;

use algebra::{Field, PrimeField, FpParameters, ToConstraintField, BigInteger};

use crate::{PoseidonParameters, SBox, SpongeMode, AlgebraicSponge, PoseidonHash};

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
        if elems.len() > 0 {
            match self.mode {
                // If we were absorbing keep doing it
                SpongeMode::Absorbing => elems.into_iter().for_each(|f| { self.update(f); }),

                // If we were squeezing, change the state into absorbing
                SpongeMode::Squeezing => {
                    self.mode = SpongeMode::Absorbing;
                    self._absorb(elems);
                }
            }
        }
    }

    /// Squeeze 'num_bits' from this sponge
    pub fn squeeze_bits(&mut self, num_bits: usize) -> Vec<bool> {
        // We return a certain amount of bits by squeezing field elements instead,
        // serialize them and return their bits.

        // Smallest number of field elements to squeeze to reach 'num_bits' is ceil(num_bits/FIELD_CAPACITY).
        // This is done to achieve uniform distribution over the output space, and it also
        // comes handy as in the circuit we don't need to enforce range proofs for them.
        let usable_bits = SpongeF::Params::CAPACITY as usize; 
        let num_elements = (num_bits + usable_bits - 1) / usable_bits;
        let src_elements = self.squeeze(num_elements);

        // Serialize field elements into bits and return them
        let mut dest_bits: Vec<bool> = Vec::with_capacity(usable_bits * num_elements);
    
        // discard leading zeros + 1 bit below modulus bits
        let skip = (SpongeF::Params::REPR_SHAVE_BITS + 1) as usize;
        for elem in src_elements.iter() {
            let elem_bits = elem.into_repr().to_bits();
            dest_bits.extend_from_slice(&elem_bits[skip..]);
        }
    
        dest_bits
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

    fn absorb<F: Field, A: ToConstraintField<F>>(&mut self, to_absorb: &A)
    {
        // Get F field elements
        let fes = to_absorb.to_field_elements().unwrap();

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
                bits.to_field_elements().unwrap()
            }
        };

        // Perform absorption
        self._absorb(elems);
    }

    fn squeeze(&mut self, num: usize) -> Vec<SpongeF> {
        let mut outputs = Vec::with_capacity(num);

        if num > 0 {
            match self.mode {
                SpongeMode::Absorbing => {
                    // If pending is empty and we were in absorbing, it means that a Poseidon
                    // permutation was applied just before calling squeeze(), (unless you absorbed
                    // nothing, but that is handled) therefore it's wasted to apply another
                    // permutation, and we can directly add state[0] to the outputs
                    if self.pending.len() == 0 {
                        outputs.push(self.state[0].clone());
                    }

                    // If pending is not empty and we were absorbing, then we need to add the
                    // pending elements to the state and then apply a permutation
                    else {
                        self.apply_permutation();
                        outputs.push(self.state[0].clone());
                    }
                    self.mode = SpongeMode::Squeezing;
                    outputs.append(&mut self.squeeze(num - 1));
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
}

#[cfg(test)]
mod test {
    use crate::crh::test::algebraic_sponge_consistency_test;

    #[cfg(feature = "tweedle")]
    #[test]
    fn test_poseidon_sponge_tweedle_fr() {
        use algebra::{fields::tweedle::{Fr as TweedleFr, Fq as TweedleFq}, BigInteger256};
        use rand::SeedableRng;
        use rand_xorshift::XorShiftRng;
        use crate::crh::poseidon::parameters::tweedle_dee::*;

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        algebraic_sponge_consistency_test::<TweedleFrPoseidonSponge, TweedleFr, TweedleFq, _>(
            rng,
            TweedleFr::new(BigInteger256([15025527542916641753, 11179691109613937013, 13666861152051537266, 3622624103826351422]))
        );
    }

    #[cfg(feature = "tweedle")]
    #[test]
    fn test_poseidon_sponge_tweedle_fq() {
        use algebra::{fields::tweedle::{Fr as TweedleFr, Fq as TweedleFq}, BigInteger256};
        use rand::SeedableRng;
        use rand_xorshift::XorShiftRng;
        use crate::crh::poseidon::parameters::tweedle_dum::*;

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
        algebraic_sponge_consistency_test::<TweedleFqPoseidonSponge, TweedleFq, TweedleFr, _>(
            rng,
            TweedleFq::new(BigInteger256([7804364686596089774, 13418158964487916491, 4784552261685790545, 2394971355270751164]))
        );
    }
}