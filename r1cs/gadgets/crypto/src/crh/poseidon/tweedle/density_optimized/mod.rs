use std::marker::PhantomData;

use crate::{FieldBasedHashGadget, AlgebraicSpongeGadget};
use algebra::fields::PrimeField;
use primitives::{crh::PoseidonParameters, PoseidonQuinticSBox, PoseidonHash, PoseidonSponge, SpongeMode, AlgebraicSponge};
use r1cs_core::{ConstraintSystemAbstract, ConstraintVar, LinearCombination, SynthesisError};
use r1cs_std::{
    alloc::{AllocGadget, ConstantGadget},
    fields::{fp::FpGadget, FieldGadget},
    Assignment, to_field_gadget_vec::ToConstraintFieldGadget,
};

pub mod constants;
pub use constants::*;

/// Poseidon Hash implementation optimized for densities, in this
/// very particular use case (e.g. SBox = x^5, R_F = 8 and R_P = 56).
/// TODO: Generalize this in terms of number of rounds.
pub struct DensityOptimizedPoseidonQuinticSboxHashGadget<
    ConstraintF: PrimeField,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
> {
    _field: PhantomData<ConstraintF>,
    _params: PhantomData<P>,
    _density_optimized_params: PhantomData<DOP>,
}

impl<ConstraintF, P, DOP> DensityOptimizedPoseidonQuinticSboxHashGadget<ConstraintF, P, DOP>
where
    ConstraintF: PrimeField,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
{
    fn enforce_multiple_full_rounds<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        state: &mut [FpGadget<ConstraintF>],
        num_rounds_to_process: usize,
        round_idx: &mut usize,
    ) -> Result<(), SynthesisError> {
        // Initialize state processing vectors.
        let mut state_pow_2 = Vec::with_capacity(P::T);
        let mut state_pow_4 = state_pow_2.clone();
        let mut state_pow_5 = state_pow_4.clone();

        for j in 0..P::T {
            let round_cst = P::ROUND_CST[*round_idx * P::T + j]; // Must take into account that round costants are stored in a single dimension collection

            // Enforce new state_pow_2 elems
            {
                // (state[j] + round_cst) * (state[j] + round_cst) == new_state_elem
                let new_state_elem = state[j]
                    .add_constant(
                        cs.ns(|| format!("compute_state_pow_2_elem_{}_add_round_cst", j)),
                        &round_cst,
                    )?
                    .square(cs.ns(|| format!("compute_state_pow_2_elem_{}_square", j)))?;

                state_pow_2.push(new_state_elem);
            }

            // Enforce new state_pow_4 elems
            {
                // state_pow_2[j] * state_pow_2[j] == new_state_elem
                let new_state_elem = state_pow_2[j]
                    .square(cs.ns(|| format!("compute_check_state_pow_4_elem_{}", j)))?;

                state_pow_4.push(new_state_elem);
            }

            // Enforce new state_pow_5 elems
            {
                // new_state_elem = (state_pow_4[j] * state[j]) + (state_pow_4[j] * round_cst)
                let new_state_elem = FpGadget::<ConstraintF>::alloc(
                    cs.ns(|| format!("compute_state_pow_5_elem_{}", j)),
                    || {
                        Ok(
                            (state[j].get_value().get()? * state_pow_4[j].get_value().get()?)
                                + (state_pow_4[j].get_value().get()? * round_cst),
                        )
                    },
                )?;

                // state[j] * state_pow_4[j] == new_state_elem - (state_pow_4[j] * round_cst)
                cs.enforce(
                    || format!("check_state_pow_5_elem_{}", j),
                    |lc| state[j].get_variable() + lc,
                    |lc| state_pow_4[j].get_variable() + lc,
                    |lc| {
                        new_state_elem.get_variable()
                            + (-round_cst, &state_pow_4[j].get_variable())
                            + lc
                    },
                );

                state_pow_5.push(new_state_elem);
            }
        }

        *round_idx += 1;

        for k in 0..num_rounds_to_process - 1 {
            let mut new_state_pow_5 = Vec::with_capacity(P::T);

            for j in 0..P::T {
                let round_cst = P::ROUND_CST[*round_idx * P::T + j];
                let mds_start_idx = P::T * j;

                // Compute MDS*state_pow_5[j] LC =
                // (MDS[j,0]·state_pow_5[0] + MDS[j,1]·state_pow_5[1] +MDS[j,2]·state_pow_5[2] + round_cst)
                let mds_times_state_pow_5_lc = {
                    let mut temp: ConstraintVar<ConstraintF> = (round_cst, CS::one()).into();
                    for t in 0..P::T {
                        temp = temp
                            + (
                                P::MDS_CST[mds_start_idx + t],
                                &state_pow_5[t].get_variable(),
                            );
                    }
                    temp
                };

                // Update state_pow_2_elems
                {
                    // new_state_elem = mds_times_state_pow_5_val^2
                    let new_state_elem = FpGadget::<ConstraintF>::alloc(
                        cs.ns(|| format!("update_state_pow_2_elem_{}_{}", j, k)),
                        || {
                            let mut val = ConstraintF::zero();

                            for t in 0..P::T {
                                val += P::MDS_CST[mds_start_idx + t]
                                    * state_pow_5[t].get_value().get()?;
                            }
                            val += round_cst;
                            Ok(val.square())
                        },
                    )?;

                    // mds_times_state_pow_5_lc * mds_times_state_pow_5_lc == new_state_elem
                    cs.enforce(
                        || format!("check_updated_state_pow_2_elem_{}_{}", j, k),
                        |lc| &mds_times_state_pow_5_lc + lc,
                        |lc| &mds_times_state_pow_5_lc + lc,
                        |lc| new_state_elem.get_variable() + lc,
                    );
                    state_pow_2[j] = new_state_elem;
                }

                // Update state_pow_4_elems
                {
                    // state_pow_2[j] * state_pow_2[j] == new_state_elem
                    let new_state_elem = state_pow_2[j]
                        .square(cs.ns(|| format!("update_check_state_pow_4_elem_{}_{}", j, k)))?;

                    state_pow_4[j] = new_state_elem;
                }

                // Compute new_state_pow_5_elems
                {
                    // new_state_elem = mds_times_state_pow_5_val * state_4[j]
                    let new_state_elem = FpGadget::<ConstraintF>::alloc(
                        cs.ns(|| format!("compute_new_state_pow_5_elem_{}_{}", j, k)),
                        || {
                            let mut val = ConstraintF::zero();

                            for t in 0..P::T {
                                val += P::MDS_CST[mds_start_idx + t]
                                    * state_pow_5[t].get_value().get()?;
                            }
                            val += round_cst;
                            Ok(val * state_pow_4[j].get_value().get()?)
                        },
                    )?;

                    // mds_times_state_pow_5_lc * state_pow_4[j] == new_state_elem
                    cs.enforce(
                        || format!("check_new_state_pow_5_elem_{}_{}", j, k),
                        |lc| &mds_times_state_pow_5_lc + lc,
                        |lc| state_pow_4[j].get_variable() + lc,
                        |lc| new_state_elem.get_variable() + lc,
                    );

                    new_state_pow_5.push(new_state_elem);
                }
            }
            state_pow_5 = new_state_pow_5;
            *round_idx += 1;
        }

        for j in 0..P::T {
            let mds_start_idx = P::T * j;

            // Compute MDS*new_state_pow_5[j] val =
            // (MDS[j,0]new_state_pow_5[0] + MDS[j,1]new_state_pow_5[1] +MDS[j,2]new_state_pow_5[2])
            let mds_times_new_state_pow_5_val = FpGadget::<ConstraintF>::alloc(
                cs.ns(|| format!("compute_mds_times_new_state_pow_5_val_{}", j)),
                || {
                    let mut val = ConstraintF::zero();

                    for t in 0..P::T {
                        val += P::MDS_CST[mds_start_idx + t] * state_pow_5[t].get_value().get()?;
                    }

                    Ok(val)
                },
            )?;

            // Compute MDS*new_state_pow_5[j] LC =
            // (MDS[j,0]new_state_pow_5[0] + MDS[j,1]new_state_pow_5[1] +MDS[j,2]new_state_pow_5[2])
            let mds_times_new_state_pow_5_lc = {
                let mut temp = ConstraintVar::<ConstraintF>::zero();
                for t in 0..P::T {
                    temp = temp
                        + (
                            P::MDS_CST[mds_start_idx + t],
                            &state_pow_5[t].get_variable(),
                        );
                }
                temp
            };

            cs.enforce(
                || format!("enforce_mds_times_new_state_pow_5_{}", j),
                |lc| lc + CS::one(),
                |lc| mds_times_new_state_pow_5_lc + lc,
                |lc| mds_times_new_state_pow_5_val.get_variable() + lc,
            );

            state[j] = mds_times_new_state_pow_5_val;
        }

        Ok(())
    }

    fn enforce_multiple_partial_rounds<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        state: &mut [FpGadget<ConstraintF>],
        num_rounds_to_process: usize,
        round_idx: &mut usize,
    ) -> Result<(), SynthesisError> {
        let mut x = vec![FpGadget::<ConstraintF>::zero(cs.ns(|| "zero"))?; num_rounds_to_process + 1];
        x[0] = state[0].clone();

        for j in 0..num_rounds_to_process {
            let round_cst = P::ROUND_CST[3 * (*round_idx + j)];

            let x_2 = x[j]
                .add_constant(
                    cs.ns(|| format!("compute_x2_{}_add_round_cst", j)),
                    &round_cst,
                )?
                .square(cs.ns(|| format!("compute_x2_{}_square", j)))?;

            let x_4 = x_2.square(cs.ns(|| format!("compute_x4_{}", j)))?;

            // Compute new state[0] elem
            {
                // x[j+1] = LC[j,0]·state[1] + LC[j,1]·state[2] + sum(k=1..j) LC[j,1+k]·x[k] + alpha[round_idx][j] +
                //          (x[j] + round_cst)*(MDS[0,0]·x4)
                let new_state_elem =
                    FpGadget::<ConstraintF>::alloc(cs.ns(|| format!("compute new x elem {}", j)), || {
                        let mut val = DOP::LC[j][0] * state[1].get_value().get()?
                            + DOP::LC[j][1] * state[2].get_value().get()?;
                        for k in 1..=j {
                            val += DOP::LC[j][k + 1] * x[k].get_value().get()?;
                        }
                        val += DOP::ALPHA[*round_idx][j]
                            + ((x[j].get_value().get()? + round_cst)
                                * (P::MDS_CST[0] * x_4.get_value().get()?));

                        Ok(val)
                    })?;

                // new_state_lc = x[j+1] - LC[j,0]·state[1] - LC[j,1]·state[2] -sum(k=1..j)(LC[j,1+k]·x[k]) - alpha[round_idx][j]
                let new_state_lc = {
                    let mut t = new_state_elem.get_variable()
                        + (-DOP::LC[j][0], &state[1].get_variable())
                        + (-DOP::LC[j][1], &state[2].get_variable());

                    for k in 1..=j {
                        t = t + (-DOP::LC[j][k + 1], &x[k].get_variable());
                    }

                    t = t + (-DOP::ALPHA[*round_idx][j], CS::one());

                    t + LinearCombination::<ConstraintF>::zero()
                };

                //  new_state_lc = (x[j] + round_cst) * (MDS[0,0]*x_4)
                cs.enforce(
                    || format!("check new x elem {}", j),
                    |lc| x[j].get_variable() + (round_cst, CS::one()) + lc,
                    |lc| (x_4.get_variable() + lc) * P::MDS_CST[0],
                    |_| new_state_lc,
                );

                x[j + 1] = new_state_elem;
            }
        }
        let new_state_0 = x[num_rounds_to_process].clone();

        // Enforce new state[1] elem
        let new_state_1 = {
            // Let n = num_rounds_to_process
            // y_val = b[n]·state[1] + c[n]·state[2] +sum(k=0..n-1)(a[k]·x[n-k]) + beta[round_idx][n]
            let y_val = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc y val"), || {
                let mut val = DOP::B[num_rounds_to_process] * state[1].get_value().get()?
                    + DOP::C[num_rounds_to_process] * state[2].get_value().get()?
                    + DOP::BETA[*round_idx][num_rounds_to_process];

                for k in 0..num_rounds_to_process {
                    val += DOP::A[k] * x[num_rounds_to_process - k].get_value().unwrap();
                }

                Ok(val)
            })?;

            // y_lc = b[n]·state[1] + c[n]·state[2] +sum(k=0..n-1)(a[k]·x[n-k]) + beta[round_idx][n]
            let y_lc = {
                let mut t: ConstraintVar<ConstraintF> =
                    (DOP::B[num_rounds_to_process], state[1].get_variable()).into();
                t = t
                    + (DOP::C[num_rounds_to_process], &state[2].get_variable())
                    + (DOP::BETA[*round_idx][num_rounds_to_process], CS::one());

                for k in 0..num_rounds_to_process {
                    t = t + (DOP::A[k], &x[num_rounds_to_process - k].get_variable())
                }
                t + LinearCombination::zero()
            };

            // 1 * b[n]·state[1] + c[n]·state[2] +sum(k=0..n-1)(a[k]·x[n-k]) + beta[round_idx][n] == y_lc
            cs.enforce(
                || "enforce y",
                |lc| lc + CS::one(),
                |_| y_lc,
                |lc| y_val.get_variable() + lc,
            );

            y_val
        };

        // Enforce new state[2] elem
        let new_state_2 = {
            // Let n = num_rounds_to_process
            // z_val = e[n]·state[1] + f[n]·state[2] +sum(k=0..n-1)(d[k]·x[n-k]) + gamma[round_idx][n]
            let z_val = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc z val"), || {
                let mut val = DOP::E[num_rounds_to_process] * state[1].get_value().get()?
                    + DOP::F[num_rounds_to_process] * state[2].get_value().get()?
                    + DOP::GAMMA[*round_idx][num_rounds_to_process];

                for k in 0..num_rounds_to_process {
                    val += DOP::D[k] * x[num_rounds_to_process - k].get_value().unwrap();
                }

                Ok(val)
            })?;

            // z_lc = e[n]·state[1] + f[n]·state[2] +sum(k=0..n-1)(d[k]·x[n-k]) + gamma[round_idx][n]
            let z_lc = {
                let mut t: ConstraintVar<ConstraintF> =
                    (DOP::E[num_rounds_to_process], state[1].get_variable()).into();
                t = t
                    + (DOP::F[num_rounds_to_process], &state[2].get_variable())
                    + (DOP::GAMMA[*round_idx][num_rounds_to_process], CS::one());

                for k in 0..num_rounds_to_process {
                    t = t + (DOP::D[k], &x[num_rounds_to_process - k].get_variable())
                }
                t + LinearCombination::zero()
            };

            // 1 * e[n]·state[1] + f[n]·state[2] +sum(k=0..n-1)(d[k]·x[n-k]) + gamma[round_idx][n] == z_lc
            cs.enforce(
                || "enforce z",
                |lc| lc + CS::one(),
                |_| z_lc,
                |lc| z_val.get_variable() + lc,
            );

            z_val
        };

        state[0] = new_state_0;
        state[1] = new_state_1;
        state[2] = new_state_2;

        *round_idx += num_rounds_to_process;

        Ok(())
    }

    fn poseidon_perm<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        state: &mut [FpGadget<ConstraintF>],
    ) -> Result<(), SynthesisError> {
        let mut round_idx = 0;

        Self::enforce_multiple_full_rounds(
            cs.ns(|| "enforce first set of full rounds"),
            state,
            P::R_F as usize,
            &mut round_idx,
        )?;

        for i in 0..P::R_P / DOP::MULTIPLE_PARTIAL_ROUNDS_LEN {
            Self::enforce_multiple_partial_rounds(
                cs.ns(|| format!("enforce set {} of partial rounds", i)),
                state,
                DOP::MULTIPLE_PARTIAL_ROUNDS_LEN as usize,
                &mut round_idx,
            )?;
        }

        Self::enforce_multiple_full_rounds(
            cs.ns(|| "enforce last set of full rounds"),
            state,
            P::R_F as usize,
            &mut round_idx,
        )?;

        assert_eq!(round_idx as i32, 2 * P::R_F + P::R_P);

        Ok(())
    }
}

// Type aliases for sake of readability
type QSB<ConstraintF, P> = PoseidonQuinticSBox<ConstraintF, P>;
type H<ConstraintF, P> = PoseidonHash<ConstraintF, P, QSB<ConstraintF, P>>;

// FieldBasedHashGadget trait implementation
impl<ConstraintF, P, DOP> FieldBasedHashGadget<H<ConstraintF, P>, ConstraintF>
    for DensityOptimizedPoseidonQuinticSboxHashGadget<ConstraintF, P, DOP>
where
    ConstraintF: PrimeField,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
{
    type DataGadget = FpGadget<ConstraintF>;

    fn enforce_hash_constant_length<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        input: &[Self::DataGadget],
    ) -> Result<Self::DataGadget, SynthesisError>
    // Assumption:
    //     capacity c = 1
    {
        assert!(P::R_F % 2 == 0);
        assert!(P::R_P % DOP::MULTIPLE_PARTIAL_ROUNDS_LEN == 0);
        assert_eq!(P::T, 3);

        if input.is_empty() {
            return Err(SynthesisError::Other(
                "Input data array does not contain any data".to_owned(),
            ));
        }

        let mut state = Vec::new();
        for i in 0..P::T {
            let elem = FpGadget::<ConstraintF>::from_value(
                cs.ns(|| format!("hardcode_state_{}", i)),
                &P::AFTER_ZERO_PERM[i],
            );
            state.push(elem);
        }

        // calculate the number of cycles to process the input dividing in portions of rate elements
        let num_cycles = input.len() / P::R;
        // check if the input is a multiple of the rate by calculating the remainder of the division
        // the remainder of dividing the input length by the rate can be 1 or 0 because we are assuming
        // that the rate is 2
        let rem = input.len() % P::R;

        // index to process the input
        let mut input_idx = 0;
        // iterate of the portions of rate elements
        for i in 0..num_cycles {
            // add the elements to the state vector. Add rate elements
            for j in 0..P::R {
                let new_state_elem = FpGadget::<ConstraintF>::alloc(
                    cs.ns(|| format!("compute_new_state_elem_{}_{}", i, j)),
                    || Ok(state[j].get_value().get()? + input[input_idx].get_value().get()?),
                )?;
                // state[j] * 1 = new_state_elem - input[input_idx]
                cs.enforce(
                    || format!("check_new_state_elem_{}_{}", i, j),
                    |lc| &state[j].get_variable() + lc,
                    |lc| lc + CS::one(),
                    |lc| new_state_elem.get_variable() - &input[input_idx].get_variable() + lc,
                );
                state[j] = new_state_elem;
                input_idx += 1;
            }
            // apply permutation after adding the input vector
            Self::poseidon_perm(cs.ns(|| format!("poseidon_perm_{}", i)), &mut state)?;
        }

        // in case the input is not a multiple of the rate, process the remainder part padding zeros
        if rem != 0 {
            for j in 0..rem {
                let new_state_elem = FpGadget::<ConstraintF>::alloc(
                    cs.ns(|| format!("padding_compute_new_state_elem_{}", j)),
                    || Ok(state[j].get_value().get()? + input[input_idx].get_value().get()?),
                )?;
                // state[j] * 1 = new_state_elem - input[input_idx]
                cs.enforce(
                    || format!("padding_check_new_state_elem_{}", j),
                    |lc| &state[j].get_variable() + lc,
                    |lc| lc + CS::one(),
                    |lc| new_state_elem.get_variable() - &input[input_idx].get_variable() + lc,
                );
                state[j] = new_state_elem;
                input_idx += 1;
            }
            // apply permutation after adding the input vector
            Self::poseidon_perm(cs.ns(|| "poseidon_padding_perm"), &mut state)?;
        }

        // return the first element of the state vector as the hash digest
        Ok(state[0].clone())
    }
}

//  TODO: Currently, below, it's just an adapted copy paste of the code from poseidon/sponge.rs
//        We can maybe save more code by defining additional traits in poseidon/sponge.rs and
//        providing default implementation.

// Type aliases for sake of readability
pub type S<ConstraintF, P> = PoseidonSponge<ConstraintF, P, QSB<ConstraintF, P>>;

/// Poseidon Sponge implementation optimized for densities, in this
/// very particular use case (e.g. SBox = x^5, R_F = 8 and R_P = 56).
/// TODO: Generalize this in terms of number of rounds.
#[derive(Clone)]
pub struct DensityOptimizedPoseidonQuinticSboxSpongeGadget<
    ConstraintF: PrimeField,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
> {
    pub(crate) mode: SpongeMode,
    pub(crate) state: Vec<FpGadget<ConstraintF>>,
    pub(crate) pending: Vec<FpGadget<ConstraintF>>,
    _parameters: PhantomData<P>,
    _density_optimized_params: PhantomData<DOP>,
}

impl<ConstraintF, P, DOP> DensityOptimizedPoseidonQuinticSboxSpongeGadget<ConstraintF, P, DOP>
where
    ConstraintF: PrimeField,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
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
        DensityOptimizedPoseidonQuinticSboxHashGadget::<ConstraintF, P, DOP>::poseidon_perm(
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

// AlgebraicSpongeGadget trait implementation
impl<ConstraintF, P, DOP> AlgebraicSpongeGadget<ConstraintF, S<ConstraintF, P>>
    for DensityOptimizedPoseidonQuinticSboxSpongeGadget<ConstraintF, P, DOP>
where
    ConstraintF: PrimeField,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
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
            _parameters: PhantomData,
            _density_optimized_params: PhantomData,
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
        to_absorb: AG
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        AG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>
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
                    self.enforce_absorb(cs, elems)?;
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

                        DensityOptimizedPoseidonQuinticSboxHashGadget::<ConstraintF, P, DOP>::poseidon_perm(
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

impl<ConstraintF, P, DOP> ConstantGadget<S<ConstraintF, P>, ConstraintF>
    for DensityOptimizedPoseidonQuinticSboxSpongeGadget<ConstraintF, P, DOP>
where
    ConstraintF: PrimeField,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
{
    fn from_value<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, value: &S<ConstraintF, P>) -> Self {
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
            _parameters: PhantomData,
            _density_optimized_params: PhantomData,
        }
    }

    fn get_constant(&self) -> S<ConstraintF, P> {
        S::<ConstraintF, P>::new(
            self.mode.clone(),
            self.state.get_constant(),
            self.pending.get_constant(),
        )
    }
}

impl<ConstraintF, P, DOP> From<Vec<FpGadget<ConstraintF>>>
for DensityOptimizedPoseidonQuinticSboxSpongeGadget<ConstraintF, P, DOP>
    where
    ConstraintF: PrimeField,
    P: PoseidonParameters<Fr = ConstraintF>,
    DOP: DensityOptimizedPoseidonQuinticSBoxParameters<ConstraintF, P>
{
    fn from(other: Vec<FpGadget<ConstraintF>>) -> Self {
        assert_eq!(other.len(), P::T);
        Self {
            mode: SpongeMode::Absorbing,
            state: other,
            pending: Vec::with_capacity(P::R),
            _parameters: PhantomData,
            _density_optimized_params: PhantomData,
        }
    }
}

use algebra::fields::tweedle::{Fr, Fq};
use crate::crh::poseidon::{
    tweedle::{TweedleFrPoseidonParameters, TweedleFqPoseidonParameters},
    density_optimized::{TweedleFrDensityOptimizedPoseidonParameters, TweedleFqDensityOptimizedPoseidonParameters}
};

pub type TweedleFrDensityOptimizedPoseidonHashGadget = DensityOptimizedPoseidonQuinticSboxHashGadget<Fr, TweedleFrPoseidonParameters, TweedleFrDensityOptimizedPoseidonParameters>;
pub type TweedleFrDensityOptimizedPoseidonSpongeGadget = DensityOptimizedPoseidonQuinticSboxSpongeGadget<Fr, TweedleFrPoseidonParameters, TweedleFrDensityOptimizedPoseidonParameters>;
pub type TweedleFqDensityOptimizedPoseidonHashGadget = DensityOptimizedPoseidonQuinticSboxHashGadget<Fq, TweedleFqPoseidonParameters, TweedleFqDensityOptimizedPoseidonParameters>;
pub type TweedleFqDensityOptimizedPoseidonSpongeGadget = DensityOptimizedPoseidonQuinticSboxSpongeGadget<Fq, TweedleFqPoseidonParameters, TweedleFqDensityOptimizedPoseidonParameters>;

#[cfg(test)]
mod test {
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use crate::crh::test::{constant_length_field_based_hash_gadget_native_test, algebraic_sponge_gadget_test};

    use super::*;

    #[test]
    fn test_density_optimized_tweedle_fr_poseidon() {
        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);

        for ins in 1..=5 {
            constant_length_field_based_hash_gadget_native_test::<_, _, TweedleFrDensityOptimizedPoseidonHashGadget, _>(rng, ins);
            algebraic_sponge_gadget_test::<Fq, Fr, _, TweedleFrDensityOptimizedPoseidonSpongeGadget, _>(rng, ins);
        }
    }

    #[test]
    fn test_density_optimized_tweedle_fq_poseidon() {
        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);

        for ins in 1..=5 {
            constant_length_field_based_hash_gadget_native_test::<_, _, TweedleFqDensityOptimizedPoseidonHashGadget, _>(rng, ins);
            algebraic_sponge_gadget_test::<Fr, Fq, _, TweedleFqDensityOptimizedPoseidonSpongeGadget, _>(rng, ins);
        }
    }
}
