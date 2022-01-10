use crate::fields::nonnative::NonNativeFieldParams;

/// The surfeit used for finding the optimal parameters
pub(crate) const SURFEIT:u32 = 10; 

/// Obtain the parameters from a `ConstraintSystem`'s cache or generate a new one
#[must_use]
pub const fn get_params(target_field_size: usize, base_field_size: usize) -> NonNativeFieldParams {
    let (num_of_limbs, limb_size, _) =
        find_parameters(base_field_size, target_field_size);
    NonNativeFieldParams {
        num_limbs: num_of_limbs,
        bits_per_limb: limb_size,
    }
}

/// Finding parameters which minimize the number of constraints of a `single mul_without_prereduce()`
/// and a subsequent `reduce()` on operand which have `surfeit = 10`, assuming that for both operands
/// ``
///     num_adds + 1 = 2^10 - 1.
/// `` 
// TODO: Let us reconsider the treatment of parameters, by introducing separate 
// NonNativeParameters, and modifying the optimum finder to use the constraint counts
// from the synthesizer. 
pub(crate) const fn find_parameters(
    base_field_prime_length: usize,
    target_field_prime_length: usize,
) -> (usize, usize, usize) {

    let mut first = true;
    let mut min_cost = 0usize;
    let mut min_cost_limb_size = 0usize;
    let mut min_cost_num_of_limbs = 0usize;

    // NOTE: with our choice of `surfeit` the following computations do 
    // not cause overflows when using `usize`. 
    let num_adds_plus_one = 2usize.pow(SURFEIT) - 1;
    let capacity = base_field_prime_length  - 1;
    let mut bits_per_limb = 1usize;

    while bits_per_limb <= target_field_prime_length - 1  {
        // we compute the number of constraints for a `single mul_without_prereduce()`
        // and a subsequent `reduce()`
        let num_limbs = (target_field_prime_length  + bits_per_limb - 1)/ bits_per_limb; 

        // computing the product representation
        let mut constraints = num_limbs * num_limbs;
        // num adds over product normal form for the product
        let num_add_prod = num_limbs 
            * num_adds_plus_one
            * num_adds_plus_one
            - 1;
        // compute the ceil_log_2 of `num_add_prod + 1`
        let mut surfeit_prod = std::mem::size_of::<u128>() * 8 - 
           ((num_add_prod + 1) as u128).leading_zeros() as usize;
        if num_add_prod + 1 == 2usize.pow((surfeit_prod - 1) as u32) {surfeit_prod -= 1}; 
        // alloc k and r 
        constraints += 2*target_field_prime_length + surfeit_prod;
        // computing k*p + r
        constraints += num_limbs * num_limbs;

        // The surfeit caused by (k*p + r)
        let num_add_kp_r = num_limbs  + num_add_prod;  
        // compute the ceil_log_2 of `num_add_kp_r + 1`
        let mut surfeit_kp_r = std::mem::size_of::<u128>() * 8 - 
           ((num_add_kp_r + 1) as u128).leading_zeros() as usize;
        if num_add_kp_r + 1 == 2usize.pow((surfeit_kp_r - 1) as u32) {surfeit_kp_r -= 1}; 
        
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
        let s =  (capacity - 2 - (2 * bits_per_limb + surfeit_kp_r))/bits_per_limb  + 1;
        // num_groups = Ceil[(2*num_limbs)/ S]
        let num_groups = (2*num_limbs + s - 1)/s;
        // ``
        //      (num_groups - 1) * (1 + 2*bits_per_limb + surfeit_kp_r + 2 - bits_per_limb) + 2
        // ``
        constraints += (num_groups - 1) * (3 + bits_per_limb + surfeit_kp_r) + 2;
                
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
