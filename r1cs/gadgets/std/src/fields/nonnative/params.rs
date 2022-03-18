use crate::fields::nonnative::NonNativeFieldParams;
use algebra::{FpParameters, PrimeField};

/// The surfeit used for finding the optimal parameters
pub(crate) const SURFEIT: u32 = 10;

/// Obtain the parameters from a `ConstraintSystem`'s cache or generate a new one
#[must_use]
pub fn get_params<SimulationF: PrimeField, ConstraintF: PrimeField>() -> NonNativeFieldParams {
    return if super::is_pseudo_mersenne::<SimulationF>() {
        get_params_for_pseudomersenne(
            SimulationF::size_in_bits(),
            ConstraintF::size_in_bits(),
            SimulationF::Params::DIFFERENCE_WITH_HIGHER_POWER_OF_TWO.unwrap(),
        )
    } else {
        get_params_for_generic_field(SimulationF::size_in_bits(), ConstraintF::size_in_bits())
    };
}

pub(crate) const fn get_params_for_pseudomersenne(
    target_field_prime_length: usize,
    base_field_prime_length: usize,
    pseudo_mersenne_const: u64,
) -> NonNativeFieldParams {
    let (num_of_limbs, limb_size, _) = find_parameters_for_pseudomersenne(
        target_field_prime_length,
        base_field_prime_length,
        pseudo_mersenne_const,
    );
    NonNativeFieldParams {
        num_limbs: num_of_limbs,
        bits_per_limb: limb_size,
    }
}

pub(crate) const fn get_params_for_generic_field(
    target_field_prime_length: usize,
    base_field_prime_length: usize,
) -> NonNativeFieldParams {
    let (num_of_limbs, limb_size, _) =
        find_parameters_for_generic_field(target_field_prime_length, base_field_prime_length);
    NonNativeFieldParams {
        num_limbs: num_of_limbs,
        bits_per_limb: limb_size,
    }
}

const fn ceil_log2(value: u128) -> usize {
    let mut result = std::mem::size_of::<u128>() * 8 - value.leading_zeros() as usize;
    if value == 2u128.pow((result - 1) as u32) {
        result -= 1
    }
    result
}

/// Finding parameters which minimize the number of constraints of a single `mul_without_prereduce()`
/// and a subsequent `reduce()` on operands with `surfeit = 10`, assuming that for both operands
/// ``
///     num_adds + 1 = 2^10.
/// ``
/// This function assumes that both operands belong to a pseudo-mersenne field
const fn find_parameters_for_pseudomersenne(
    target_field_prime_length: usize,
    base_field_prime_length: usize,
    pseudo_mersenne_const: u64,
) -> (usize, usize, usize) {
    let mut first = true;
    let mut min_cost = 0usize;
    let mut min_cost_limb_size = 0usize;
    let mut min_cost_num_of_limbs = 0usize;
    let num_adds_plus_one = 2u128.pow(SURFEIT);
    let capacity = base_field_prime_length - 1;

    let mut bits_per_limb = 2usize;

    while bits_per_limb <= target_field_prime_length - 1 {
        // we compute the number of constraints for a `single mul_without_prereduce()`
        // and a subsequent `reduce()`
        let num_limbs = (target_field_prime_length + bits_per_limb - 1) / bits_per_limb;
        let h = bits_per_limb * num_limbs - target_field_prime_length;
        // cost of mul
        let mut constraints = num_limbs * num_limbs;
        // compute surfeit_prod in a compatible way with const function:
        // surfeit_prod = 1 + log(num_limbs*(num_adds+1)*(num_adds+1)*(c*2^h+1)*2^bits_per_limb + 2)
        // surfeit_prod may overflow u128 if bits_per_limb is high
        let surfeit_prod = if bits_per_limb + h < 32 {
            // in this case we can compute num_adds_prod without overflowing, as num_limbs*(num_adds+1)*(num_adds+1)*(c+1) < 2^96 with our choice of surfeit
            let num_adds_prod: u128 = (num_limbs as u128 * num_adds_plus_one * num_adds_plus_one)
                * (pseudo_mersenne_const as u128 * 2u128.pow(h as u32) + 1)
                * 2u128.pow(bits_per_limb as u32)
                - 1;
            ceil_log2(num_adds_prod + 3) + 1
        } else {
            // otherwise, we compute the log without explicitly computing num_adds_prod:
            // given num_adds_unshifted = num_limbs*(num_adds+1)*(num_adds+1), we need
            // to compute 1+log(num_adds_unshifted*(c*2^h+1)*2^bits_per_limb + 2). Since num_adds_unshifted
            // must be shifted by bits_per_limb, we can neglect the addition with 2 and compute
            // log(num_adds_unshifted*2^bits_per_limb + 2) = log(num_adds_unshifted*(c*2^h+1))+bits_per_limb.
            // To compute log(num_adds_unshifted), we consider that
            // num_adds_unshifted*(c*2^h+1) = num_adds_unshifted*c*2^h + num_adds_unshifted.
            // Since num_adds_unshifted < 2^31 and c < 2^64, then if h < 32, num_adds_unshifted*(c*2^h+1)
            // can be computed without overflow. Otherwise, if h >= 32, then
            // log(num_adds_unshifted*(c*2^h+1)) = log(num_adds_unshifted*c*2^h) = log(num_adds_unshifted*c)+h
            let log_num_adds_unshifted = if h < 32 {
                let num_adds_unshifted: u128 = num_limbs as u128
                    * num_adds_plus_one
                    * num_adds_plus_one
                    * (pseudo_mersenne_const as u128 * 2u128.pow(h as u32) + 1);
                128 - num_adds_unshifted.leading_zeros() as usize
                // NOTE: no need to apply correction to the result if num_adds_unshifted is a power of two,
                // since num_adds_unshifted*2^bits_per_limb + 2 is never a power of two
            } else {
                let num_adds_unshifted: u128 = num_limbs as u128
                    * num_adds_plus_one
                    * num_adds_plus_one
                    * pseudo_mersenne_const as u128;
                128 - num_adds_unshifted.leading_zeros() as usize + h
            };
            log_num_adds_unshifted + 1 + bits_per_limb
        };
        if surfeit_prod + bits_per_limb > capacity - 2 {
            bits_per_limb += 1;
            continue;
        }
        // estimate cost of reduce
        constraints += target_field_prime_length + num_limbs; // allocate bits for reduced field element
        constraints += surfeit_prod + 1; // allocate bits for k
                                         // estimate cost of group_and_check_equality
        let s = (capacity - 2 - surfeit_prod) / bits_per_limb;
        let num_groups = (num_limbs + s - 1) / s; // equivalent to Ceil(num_limbs/s)
        constraints += (num_groups - 1) * (surfeit_prod + 4) + 2;

        if first || constraints < min_cost {
            first = false;
            min_cost = constraints;
            min_cost_limb_size = bits_per_limb;
            min_cost_num_of_limbs = num_limbs;
        }
        bits_per_limb += 1;
    }

    (min_cost_num_of_limbs, min_cost_limb_size, min_cost)
}

/// Finding parameters which minimize the number of constraints of a single `mul_without_prereduce()`
/// and a subsequent `reduce()` on operands with `surfeit = 10`, assuming that for both operands
/// ``
///     num_adds + 1 = 2^10.
/// ``
/// This function assumes that both operands belong to a non pseudo-mersenne field
const fn find_parameters_for_generic_field(
    target_field_prime_length: usize,
    base_field_prime_length: usize,
) -> (usize, usize, usize) {
    let mut first = true;
    let mut min_cost = 0usize;
    let mut min_cost_limb_size = 0usize;
    let mut min_cost_num_of_limbs = 0usize;
    // NOTE: with our choice of `surfeit` the following computations do
    // not cause overflows when using `usize`.
    let num_adds_plus_one = 2usize.pow(SURFEIT);
    let capacity = base_field_prime_length - 1;

    let mut bits_per_limb = 2usize;

    while bits_per_limb <= target_field_prime_length - 1 {
        // we compute the number of constraints for a `single mul_without_prereduce()`
        // and a subsequent `reduce()`
        let num_limbs = (target_field_prime_length + bits_per_limb - 1) / bits_per_limb;

        // computing the product representation
        let mut constraints = num_limbs * num_limbs;
        // num adds over product normal form for the product
        let num_add_prod = num_limbs * num_adds_plus_one * num_adds_plus_one - 1;
        // compute the ceil_log_2 of `num_add_prod + 1`
        let surfeit_prod = ceil_log2((num_add_prod + 1) as u128);
        // alloc k and r
        constraints += 2 * target_field_prime_length + surfeit_prod + 1 + num_limbs;

        // The surfeit caused by (k*p + r)
        let num_add_kp_r = num_limbs + 2 * (num_add_prod + 1);
        // compute the ceil_log_2 of `num_add_kp_r + 1`
        let mut surfeit_kp_r =
            std::mem::size_of::<u128>() * 8 - ((num_add_kp_r + 1) as u128).leading_zeros() as usize;
        if num_add_kp_r + 1 == 2usize.pow((surfeit_kp_r - 1) as u32) {
            surfeit_kp_r -= 1
        };

        // check if the security assumption holds, if not continue
        // jump to the start of the loop
        if 2 * bits_per_limb + surfeit_kp_r > capacity - 2 {
            bits_per_limb += 1;
            continue;
        }
        // The number of limbs per group.
        // ``
        //    S - 1 = Floor[
        //          (ConstraintF::CAPACITY - 2 - (2*bits_per_limb + surfeit')) / bits_per_limb
        //          ].
        // ``
        let s = (capacity - 2 - (2 * bits_per_limb + surfeit_kp_r)) / bits_per_limb + 1;
        // num_groups = Ceil[(2*num_limbs-1)/ S]
        let num_groups = (2 * num_limbs - 1 + s - 1) / s;
        // ``
        //      (num_groups - 1) * (1 + 2*bits_per_limb + surfeit_kp_r + 2 - bits_per_limb) + 2
        // ``
        constraints += (num_groups - 1) * (4 + bits_per_limb + surfeit_kp_r) + 2;

        if first || constraints < min_cost {
            first = false;
            min_cost = constraints;
            min_cost_limb_size = bits_per_limb;
            min_cost_num_of_limbs = num_limbs;
        }
        bits_per_limb += 1;
    }

    (min_cost_num_of_limbs, min_cost_limb_size, min_cost)
}

#[cfg(test)]
pub(crate) fn find_parameters<SimulationF: PrimeField, ConstraintF: PrimeField>(
) -> (usize, usize, usize) {
    return if let Some(c) = SimulationF::Params::DIFFERENCE_WITH_HIGHER_POWER_OF_TWO {
        find_parameters_for_pseudomersenne(
            SimulationF::size_in_bits(),
            ConstraintF::size_in_bits(),
            c,
        )
    } else {
        find_parameters_for_generic_field(SimulationF::size_in_bits(), ConstraintF::size_in_bits())
    };
}

// This test is only useful to print the constraints gain with and without pseudo-mersenne optimization.
#[cfg(test)]
pub(crate) fn test_different_constraint<
    SimulationF: PrimeField,
    ConstraintF: PrimeField,
    R: rand::RngCore,
>(
    _rng: &mut R,
) {
    let (num_limbs, bits_per_limb, constraints) = find_parameters_for_pseudomersenne(
        SimulationF::size_in_bits(),
        ConstraintF::size_in_bits(),
        SimulationF::Params::DIFFERENCE_WITH_HIGHER_POWER_OF_TWO.unwrap(),
    );

    let (num_limbs_unopt, bits_per_limb_unopt, constraints_unopt) =
        find_parameters_for_generic_field(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

    println!(
        "optimized: num limbs={}, bits_per_limb={}, cost={}, h={}",
        num_limbs,
        bits_per_limb,
        constraints,
        num_limbs * bits_per_limb - SimulationF::size_in_bits()
    );
    println!(
        "unoptimized: num limbs={}, bits_per_limb={}, cost={}",
        num_limbs_unopt, bits_per_limb_unopt, constraints_unopt
    );
}
