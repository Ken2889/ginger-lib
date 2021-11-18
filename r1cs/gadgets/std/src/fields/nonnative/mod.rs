//! A module for simulating non-native field arithmetics according to [Kosba et al.](https://ieeexplore.ieee.org/document/8418647),
//! using some of the optimizations from [Ozdemir et al.](https://eprint.iacr.org/2019/1494).
//! Ported from [arkworks/nonnative](https://github.com/arkworks-rs/nonnative).
//! The following types are defined/supported:
//! - `NonNativeFieldParams` specifies the constraint prime field (called `ConstraintF`),
//!     the simulated prime field (called `SimulationF`), and internal parameters.
//! - `NonNativeFieldGadget` implements the `FieldGadget` for simulating `SimulationF`
//!     arithmetic within `ConstraintF`.
//! - `NonNativeFieldMulResultGadget` is an intermediate representations of the
//!     result of multiplication, which is hidden from the `FieldGadget` interface
//!     and is left for advanced users who want better performance.
//! DISCLAIMER: THIS LIBRARY IS EXPERIMENTAL AND NEEDS TO UNDERGO A MORE IN-DEPTH REVIEW
use std::fmt::Debug;

pub mod params;

/// a submodule for reducing the representations
pub mod reduce;

/// the main module, non-native field gadgets and its arithmetic operations
pub mod nonnative_field_gadget;

/// The intermediate non-normalized representation resulting from products.
pub mod nonnative_field_mul_result_gadget;

#[cfg(test)]
mod tests;

/// a macro for computing the bit length ceil(log2(x)) of a field element x
#[doc(hidden)]
#[macro_export]
macro_rules! overhead {
    ($x:expr) => {{
        use algebra::BigInteger;
        let num = $x;
        let num_bits = num.into_repr().to_bits();
        let mut skipped_bits = 0;
        for b in num_bits.iter() {
            if *b == false {
                skipped_bits += 1;
            } else {
                break;
            }
        }

        let mut is_power_of_2 = true;
        for b in num_bits.iter().skip(skipped_bits + 1) {
            if *b == true {
                is_power_of_2 = false;
            }
        }

        if is_power_of_2 {
            num_bits.len() - skipped_bits
        } else {
            num_bits.len() - skipped_bits + 1
        }
    }};
}

/// Parameters for a specific `NonNativeFieldGadget` instantiation
#[derive(Copy, Clone, Debug)]
pub struct NonNativeFieldParams {
    /// The number of limbs (`ConstraintF` elements) used to represent a `SimulationF` element. Highest limb first.
    pub num_limbs: usize,

    /// The `native' number of bits of a limb.
    pub bits_per_limb: usize,
}
