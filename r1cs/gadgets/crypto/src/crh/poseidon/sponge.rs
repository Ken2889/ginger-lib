use primitives::PoseidonSponge;
use crate::crh::{*, poseidon::*};


#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct PoseidonSpongeGadget
<
    ConstraintF: PrimeField,
    P:           PoseidonParameters<Fr = ConstraintF>,
    SB:          SBox<Field = ConstraintF, Parameters = P>,
    SBG:         SBoxGadget<ConstraintF, SB>,
>
{
    pub(crate) mode:    SpongeMode,
    pub(crate) state:   Vec<FpGadget<ConstraintF>>,
    pub(crate) pending: Vec<FpGadget<ConstraintF>>,
    _field:             PhantomData<ConstraintF>,
    _parameters:        PhantomData<P>,
    _sbox:              PhantomData<SB>,
    _sbox_gadget:       PhantomData<SBG>,
}

impl<ConstraintF, P, SB, SBG> PoseidonSpongeGadget<ConstraintF, P, SB, SBG>
    where
        ConstraintF: PrimeField,
        P:           PoseidonParameters<Fr = ConstraintF>,
        SB:          SBox<Field = ConstraintF, Parameters = P>,
        SBG:         SBoxGadget<ConstraintF, SB>,
{
    fn enforce_permutation<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS
    ) -> Result<(), SynthesisError>
    {
        // add the elements to the state vector. Add rate elements
        for (i, (input, state)) in self.pending.iter().zip(self.state.iter_mut()).enumerate() {
            state.add_in_place(cs.ns(|| format!("add_input_{}_to_state", i)), input)?;
        }

        // apply permutation after adding the input vector
        PoseidonHashGadget::<ConstraintF, P, SB, SBG>::poseidon_perm(
            cs.ns(|| "poseidon_perm"),
            &mut self.state
        )?;

        self.pending.clear();

        Ok(())
    }

    fn enforce_update<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        cs: CS,
        input: FpGadget<ConstraintF>,
    ) -> Result<(), SynthesisError>
    {
        self.pending.push(input);
        if self.pending.len() == P::R {
            self.enforce_permutation(cs)?;
        }
        Ok(())
    }

    fn _enforce_absorb<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS,
        elems: Vec<FpGadget<ConstraintF>>,
    ) -> Result<(), SynthesisError>
    {
        match self.mode {
            SpongeMode::Absorbing => {
                // If we were absorbing keep doing it
                elems.iter().enumerate().map(|(i, f)| {
                    self.enforce_update(cs.ns(|| format!("update_{}", i)), f.clone())
                }).collect::<Result<(), SynthesisError>>()?;
            },

            SpongeMode::Squeezing => {
                // If we were squeezing, change the mode into absorbing
                self.mode = SpongeMode::Absorbing;
                self._enforce_absorb(cs, elems)?;
            }
        }

        Ok(())
    }

    fn _enforce_squeeze<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS,
        num: usize
    ) -> Result<Vec<FpGadget<ConstraintF>>, SynthesisError> 
    {
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
                        self.enforce_permutation(
                            cs.ns(|| "permutation")
                        )?;
                    }
                    outputs.push(self.state[0].clone());
                    
                    self.mode = SpongeMode::Squeezing;
                    outputs.append(&mut self._enforce_squeeze(
                        cs.ns(|| "squeeze remaining elements"),
                        num - 1
                    )?);
                },

                // If we were squeezing, then squeeze the required number of field elements
                SpongeMode::Squeezing => {
                    debug_assert!(self.pending.is_empty());

                    for i in 0..num {
                        PoseidonHashGadget::<ConstraintF, P, SB, SBG>::poseidon_perm(
                            cs.ns(|| format!("poseidon_perm_{}", i)),
                            &mut self.state
                        )?;
                        outputs.push(self.state[0].clone());
                    }
                }
            }
        }
        Ok(outputs)
    }
}

impl<ConstraintF, P, SB, SBG> AlgebraicSpongeGadget<ConstraintF, PoseidonSponge<ConstraintF, P, SB>>
for PoseidonSpongeGadget<ConstraintF, P, SB, SBG>
    where
        ConstraintF: PrimeField,
        P:           PoseidonParameters<Fr = ConstraintF>,
        SB:          SBox<Field = ConstraintF, Parameters = P>,
        SBG:         SBoxGadget<ConstraintF, SB>,
{
    type StateGadget = FpGadget<ConstraintF>;

    fn new<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS) -> Result<Self, SynthesisError> {
        let mut state = Vec::with_capacity(P::T);
        for i in 0..P::T {
            let elem = FpGadget::<ConstraintF>::from_value(
                cs.ns(|| format!("hardcode_state_{}",i)),
                &P::AFTER_ZERO_PERM[i]
            );
            state.push(elem);
        }

        Ok(Self {
            mode: SpongeMode::Absorbing,
            state,
            pending: Vec::with_capacity(P::R),
            _field: PhantomData,
            _parameters: PhantomData,
            _sbox: PhantomData,
            _sbox_gadget: PhantomData
        })
    }

    fn get_state(&self) -> Vec<FpGadget<ConstraintF>> {
        self.state.clone()
    }

    fn set_state(&mut self, state: Vec<FpGadget<ConstraintF>>) {
        assert_eq!(state.len(), P::T);
        self.state = state;
    }

    fn get_mode(&self) -> &SpongeMode {
        &self.mode
    }

    fn set_mode(&mut self, mode: SpongeMode) {
        self.mode = mode;
    }

    fn enforce_absorb<CS, AG>(
        &mut self,
        mut cs: CS,
        to_absorb: AG
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        AG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>
    {
        let elems = to_absorb.to_field_gadget_elements(cs.ns(|| "absorbable to fes"))?;
        
        if elems.is_empty() {
            return Err(SynthesisError::Other("Noting to absorb !".to_string()));
        }

        self._enforce_absorb(cs, elems)
    }

    fn enforce_squeeze<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        cs: CS,
        num: usize
    ) -> Result<Vec<FpGadget<ConstraintF>>, SynthesisError> 
    {
        if num == 0 {
            return Err(SynthesisError::Other("Nothing to squeeze !".to_string()));
        }

        self._enforce_squeeze(cs, num)
    }
}

impl<ConstraintF, P, SB, SBG> ConstantGadget<PoseidonSponge<ConstraintF, P, SB>, ConstraintF>
for PoseidonSpongeGadget<ConstraintF, P, SB, SBG>
    where
        ConstraintF: PrimeField,
        P:           PoseidonParameters<Fr = ConstraintF>,
        SB:          SBox<Field = ConstraintF, Parameters = P>,
        SBG:         SBoxGadget<ConstraintF, SB>,
{
    fn from_value<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, value: &PoseidonSponge<ConstraintF, P, SB>) -> Self {
        let state_g = Vec::<FpGadget<ConstraintF>>::from_value(
            cs.ns(|| "hardcode state"),
            &value.get_state().to_vec()
        );

        let pending_g = Vec::<FpGadget<ConstraintF>>::from_value(
            cs.ns(|| "hardcode pending"),
            &value.get_pending().to_vec()
        );

        Self {
            mode: value.get_mode().clone(),
            state: state_g,
            pending: pending_g,
            _field: PhantomData,
            _parameters: PhantomData,
            _sbox: PhantomData,
            _sbox_gadget: PhantomData
        }
    }

    fn get_constant(&self) -> PoseidonSponge<ConstraintF, P, SB> {
        PoseidonSponge::<ConstraintF, P, SB>::new(
            self.mode.clone(),
            self.state.get_constant(),
            self.pending.get_constant(),
        )
    }
}

impl<ConstraintF, P, SB, SBG> From<Vec<FpGadget<ConstraintF>>>
for PoseidonSpongeGadget<ConstraintF, P, SB, SBG>
    where
        ConstraintF: PrimeField,
        P:           PoseidonParameters<Fr = ConstraintF>,
        SB:          SBox<Field = ConstraintF, Parameters = P>,
        SBG:         SBoxGadget<ConstraintF, SB>,
{
    fn from(other: Vec<FpGadget<ConstraintF>>) -> Self {
        assert_eq!(other.len(), P::T);
        Self {
            mode: SpongeMode::Absorbing,
            state: other,
            pending: Vec::with_capacity(P::R),
            _field: PhantomData,
            _parameters: PhantomData,
            _sbox: PhantomData,
            _sbox_gadget: PhantomData
        }
    }
}

#[cfg(all(test, feature = "tweedle"))]
pub(crate) mod test {
    use algebra::fields::tweedle::{Fr as TweedleFr, Fq as TweedleFq};
    use primitives::{TweedleFrPoseidonParameters, PoseidonQuinticSBox, FieldBasedHashParameters, TweedleFqPoseidonParameters};
    use r1cs_core::ConstraintSystem;
    use crate::crh::test::algebraic_sponge_gadget_test;
    use super::*;
    use rand::{SeedableRng, RngCore};
    use rand_xorshift::XorShiftRng;

    // TODO: Is the behavior of this implementation of Sponge consistent with its specifications as crypto primitive ?
    //       Maybe it has to do with definition of state: the whole Sponge state should include also the pending elements
    //       formally.
    fn poseidon_sponge_gadget_test<ConstraintF, P, SB, SBG, R>(rate: usize, rng: &mut R)
    where
        ConstraintF: PrimeField,
        P:           PoseidonParameters<Fr = ConstraintF>,
        SB:          SBox<Field = ConstraintF, Parameters = P>,
        SBG:         SBoxGadget<ConstraintF, SB>,
        R:           RngCore,
    {
        let mut cs = ConstraintSystem::<ConstraintF>::new(r1cs_core::SynthesisMode::Debug);
        let mut sponge = PoseidonSpongeGadget::<ConstraintF, P, SB, SBG>::new(cs.ns(|| "init sponge")).unwrap();
        let mut prev_state = sponge.get_state();

        let fes = (0..rate)
            .map(|i| FpGadget::alloc(
                cs.ns(|| format!("alloc random fe {}", i)),
                || Ok(ConstraintF::rand(rng))
            ).unwrap()).collect::<Vec<_>>();

        // Assert that, before absorbing rate elements, state doesn't change.
        sponge.enforce_absorb(cs.ns(|| "absorb rate - 1 elems"), fes[..rate-1].to_vec()).unwrap();
        assert_eq!(sponge.get_state(), prev_state.clone());
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));
        prev_state = sponge.get_state();

        // After having absorbed rate elements a permutation is triggered and the state changes
        sponge.enforce_absorb(cs.ns(|| "absorb one more element to reach rate many"), fes[rate - 1].clone()).unwrap();
        assert_ne!(sponge.get_state(), prev_state.clone());
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));
        prev_state = sponge.get_state();

        // Assert that, calling squeeze() after absorbing rate elements doesn't change the state.
        sponge.enforce_squeeze(cs.ns(|| "squeeze after permutation"), 1).unwrap();
        assert!(matches!(sponge.get_mode(), SpongeMode::Squeezing));
        assert_eq!(prev_state.clone(), sponge.get_state());

        // Assert that the next squeeze() should instead change the state
        sponge.enforce_squeeze(cs.ns(|| "squeeze one more"), 1).unwrap();
        assert!(matches!(sponge.get_mode(), SpongeMode::Squeezing));
        assert_ne!(prev_state, sponge.get_state());
    }

    #[test]
    fn poseidon_tweedle_fr_gadget_test() {

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);

        for ins in 1..=5 {
            algebraic_sponge_gadget_test::<TweedleFq, TweedleFr, _, TweedleFrPoseidonSpongeGadget, _>(rng, ins);
        }

        poseidon_sponge_gadget_test::<
            TweedleFr,
            TweedleFrPoseidonParameters,
            PoseidonQuinticSBox<TweedleFr, TweedleFrPoseidonParameters>,
            QuinticSBoxGadget<TweedleFr, PoseidonQuinticSBox<TweedleFr, TweedleFrPoseidonParameters>>,
            _
        >(
            TweedleFrPoseidonParameters::R,
            rng,
        );
    }

    #[test]
    fn poseidon_tweedle_fq_gadget_test() {

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);

        for ins in 1..=5 {
            algebraic_sponge_gadget_test::<TweedleFr, TweedleFq, _, TweedleFqPoseidonSpongeGadget, _>(rng, ins);
        }

        poseidon_sponge_gadget_test::<
            TweedleFq,
            TweedleFqPoseidonParameters,
            PoseidonQuinticSBox<TweedleFq, TweedleFqPoseidonParameters>,
            QuinticSBoxGadget<TweedleFq, PoseidonQuinticSBox<TweedleFq, TweedleFqPoseidonParameters>>,
            _
        >(
            TweedleFqPoseidonParameters::R,
            rng,
        );
    }
}