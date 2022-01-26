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

    fn get_state(&self) -> &[FpGadget<ConstraintF>] {
        &self.state
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
        to_absorb: &AG
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        AG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>
            + ToBytesGadget<ConstraintF>
    {
        let elems = to_absorb.to_field_gadget_elements(cs.ns(|| "absorbable to fes"))?;
        if elems.len() > 0 {
            match self.mode {

                SpongeMode::Absorbing => {
                    elems.iter().enumerate().map(|(i, f)| {
                        self.enforce_update(cs.ns(|| format!("update_{}", i)), f.clone())
                    }).collect::<Result<(), SynthesisError>>()?;
                },

                SpongeMode::Squeezing => {
                    self.mode = SpongeMode::Absorbing;
                    self.enforce_absorb(cs, &elems)?;
                }
            }
        }

        Ok(())
    }

    fn enforce_squeeze<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS,
        num: usize
    ) -> Result<Vec<FpGadget<ConstraintF>>, SynthesisError> 
    {
        let mut outputs = Vec::with_capacity(num);

        if num > 0 {
            match self.mode {
                SpongeMode::Absorbing => {

                    if self.pending.len() == 0 {
                        outputs.push(self.state[0].clone());
                    } else {
                        self.enforce_permutation(
                            cs.ns(|| "permutation")
                        )?;

                        outputs.push(self.state[0].clone());
                    }
                    self.mode = SpongeMode::Squeezing;
                    outputs.append(&mut self.enforce_squeeze(
                        cs.ns(|| "squeeze remaining elements"),
                        num - 1
                    )?);
                },

                // If we were squeezing, then squeeze the required number of field elements
                SpongeMode::Squeezing => {
                    for i in 0..num {
                        debug_assert!(self.pending.len() == 0);

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