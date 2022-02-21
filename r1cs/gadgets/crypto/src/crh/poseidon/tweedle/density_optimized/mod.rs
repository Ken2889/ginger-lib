use crate::FieldBasedHashGadget;
use algebra::fields::{tweedle::Fr, Field};
use primitives::crh::{FieldBasedHashParameters, PoseidonParameters, TweedleFrPoseidonHash};
use r1cs_core::{ConstraintSystemAbstract, ConstraintVar, LinearCombination, SynthesisError};
use r1cs_std::{
    alloc::{AllocGadget, ConstantGadget},
    fields::{fp::FpGadget, FieldGadget},
    Assignment,
};

mod constants;
use constants::*;

/// Poseidon Hash implementation optimized for densities, in this
/// very particular use case (e.g. SBox = x^5, R_F = 8 and R_P = 56).
/// Might be generalizable, for the moment it isn't and it's not of
/// our interest to do so, but we tried to reduce as much as possible
/// the usage of magic numbers in favor of trait constants and use
/// generic functions.
pub struct TweedleFrDensityOptimizedPoseidonHashGadget {}

impl TweedleFrDensityOptimizedPoseidonHashGadget {
    fn enforce_multiple_full_rounds<CS: ConstraintSystemAbstract<Fr>>(
        mut cs: CS,
        state: &mut [FpGadget<Fr>],
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
                let new_state_elem = FpGadget::<Fr>::alloc(
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
                    let mut temp: ConstraintVar<Fr> = (round_cst, CS::one()).into();
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
                    let new_state_elem = FpGadget::<Fr>::alloc(
                        cs.ns(|| format!("update_state_pow_2_elem_{}_{}", j, k)),
                        || {
                            let mut val = Fr::zero();

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
                    let new_state_elem = FpGadget::<Fr>::alloc(
                        cs.ns(|| format!("compute_new_state_pow_5_elem_{}_{}", j, k)),
                        || {
                            let mut val = Fr::zero();

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
            let mds_times_new_state_pow_5_val = FpGadget::<Fr>::alloc(
                cs.ns(|| format!("compute_mds_times_new_state_pow_5_val_{}", j)),
                || {
                    let mut val = Fr::zero();

                    for t in 0..P::T {
                        val += P::MDS_CST[mds_start_idx + t] * state_pow_5[t].get_value().get()?;
                    }

                    Ok(val)
                },
            )?;

            // Compute MDS*new_state_pow_5[j] LC =
            // (MDS[j,0]new_state_pow_5[0] + MDS[j,1]new_state_pow_5[1] +MDS[j,2]new_state_pow_5[2])
            let mds_times_new_state_pow_5_lc = {
                let mut temp = ConstraintVar::<Fr>::zero();
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

    fn enforce_multiple_partial_rounds<CS: ConstraintSystemAbstract<Fr>>(
        mut cs: CS,
        state: &mut [FpGadget<Fr>],
        num_rounds_to_process: usize,
        round_idx: &mut usize,
    ) -> Result<(), SynthesisError> {
        let mut x = vec![FpGadget::<Fr>::zero(cs.ns(|| "zero"))?; num_rounds_to_process + 1];
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
                    FpGadget::<Fr>::alloc(cs.ns(|| format!("compute new x elem {}", j)), || {
                        let mut val = LC[j][0] * state[1].get_value().get()?
                            + LC[j][1] * state[2].get_value().get()?;
                        for k in 1..=j {
                            val += LC[j][k + 1] * x[k].get_value().get()?;
                        }
                        val += ALPHA[*round_idx][j]
                            + ((x[j].get_value().get()? + round_cst)
                                * (P::MDS_CST[0] * x_4.get_value().get()?));

                        Ok(val)
                    })?;

                // new_state_lc = x[j+1] - LC[j,0]·state[1] - LC[j,1]·state[2] -sum(k=1..j)(LC[j,1+k]·x[k]) - alpha[round_idx][j]
                let new_state_lc = {
                    let mut t = new_state_elem.get_variable()
                        + (-LC[j][0], &state[1].get_variable())
                        + (-LC[j][1], &state[2].get_variable());

                    for k in 1..=j {
                        t = t + (-LC[j][k + 1], &x[k].get_variable());
                    }

                    t = t + (-ALPHA[*round_idx][j], CS::one());

                    t + LinearCombination::<Fr>::zero()
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
            let y_val = FpGadget::<Fr>::alloc(cs.ns(|| "alloc y val"), || {
                let mut val = B[num_rounds_to_process] * state[1].get_value().get()?
                    + C[num_rounds_to_process] * state[2].get_value().get()?
                    + BETA[*round_idx][num_rounds_to_process];

                for k in 0..num_rounds_to_process {
                    val += A[k] * x[num_rounds_to_process - k].get_value().unwrap();
                }

                Ok(val)
            })?;

            // y_lc = b[n]·state[1] + c[n]·state[2] +sum(k=0..n-1)(a[k]·x[n-k]) + beta[round_idx][n]
            let y_lc = {
                let mut t: ConstraintVar<Fr> =
                    (B[num_rounds_to_process], state[1].get_variable()).into();
                t = t
                    + (C[num_rounds_to_process], &state[2].get_variable())
                    + (BETA[*round_idx][num_rounds_to_process], CS::one());

                for k in 0..num_rounds_to_process {
                    t = t + (A[k], &x[num_rounds_to_process - k].get_variable())
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
            let z_val = FpGadget::<Fr>::alloc(cs.ns(|| "alloc z val"), || {
                let mut val = E[num_rounds_to_process] * state[1].get_value().get()?
                    + F[num_rounds_to_process] * state[2].get_value().get()?
                    + GAMMA[*round_idx][num_rounds_to_process];

                for k in 0..num_rounds_to_process {
                    val += D[k] * x[num_rounds_to_process - k].get_value().unwrap();
                }

                Ok(val)
            })?;

            // z_lc = e[n]·state[1] + f[n]·state[2] +sum(k=0..n-1)(d[k]·x[n-k]) + gamma[round_idx][n]
            let z_lc = {
                let mut t: ConstraintVar<Fr> =
                    (E[num_rounds_to_process], state[1].get_variable()).into();
                t = t
                    + (F[num_rounds_to_process], &state[2].get_variable())
                    + (GAMMA[*round_idx][num_rounds_to_process], CS::one());

                for k in 0..num_rounds_to_process {
                    t = t + (D[k], &x[num_rounds_to_process - k].get_variable())
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

    fn poseidon_perm<CS: ConstraintSystemAbstract<Fr>>(
        mut cs: CS,
        state: &mut [FpGadget<Fr>],
    ) -> Result<(), SynthesisError> {
        let mut round_idx = 0;

        Self::enforce_multiple_full_rounds(
            cs.ns(|| "enforce first set of full rounds"),
            state,
            P::R_F as usize,
            &mut round_idx,
        )?;

        for i in 0..P::R_P / MULTIPLE_PARTIAL_ROUNDS_LEN {
            Self::enforce_multiple_partial_rounds(
                cs.ns(|| format!("enforce set {} of partial rounds", i)),
                state,
                MULTIPLE_PARTIAL_ROUNDS_LEN as usize,
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

impl FieldBasedHashGadget<TweedleFrPoseidonHash, Fr>
    for TweedleFrDensityOptimizedPoseidonHashGadget
{
    type DataGadget = FpGadget<Fr>;

    fn enforce_hash_constant_length<CS: ConstraintSystemAbstract<Fr>>(
        mut cs: CS,
        input: &[Self::DataGadget],
    ) -> Result<Self::DataGadget, SynthesisError>
// Assumption:
    //     capacity c = 1
    {
        assert!(P::R_F % 2 == 0);
        assert!(P::R_P % MULTIPLE_PARTIAL_ROUNDS_LEN == 0);
        assert_eq!(P::T, 3);

        if input.is_empty() {
            return Err(SynthesisError::Other(
                "Input data array does not contain any data".to_owned(),
            ));
        }

        let mut state = Vec::new();
        for i in 0..P::T {
            let elem = FpGadget::<Fr>::from_value(
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
                let new_state_elem = FpGadget::<Fr>::alloc(
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
                let new_state_elem = FpGadget::<Fr>::alloc(
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

#[cfg(test)]
mod test {
    use crate::{
        crh::test::constant_length_field_based_hash_gadget_native_test,
        poseidon::test::generate_inputs,
    };

    use super::*;

    #[test]
    fn test_native_density_optimized_tweedle_fr_poseidon_hash() {
        for ins in 1..=3 {
            println!("Test num inputs: {}", ins);
            constant_length_field_based_hash_gadget_native_test::<
                _,
                _,
                TweedleFrDensityOptimizedPoseidonHashGadget,
            >(generate_inputs(ins));
        }
    }
}
