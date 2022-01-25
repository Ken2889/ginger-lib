/// This module contains the implementation of three structs:
///
/// - `NonNativeFieldParams` specifies the constraint prime field (called `ConstraintF`),
///     the simulated prime field (called `SimulationF`), and internal parameters.
/// - `NonNativeFieldGadget` implements the `FieldGadget` for simulating `SimulationF`
///     arithmetic within `ConstraintF`.
/// - `NonNativeFieldMulResultGadget` is an intermediate representations of the
///     result of multiplication, which is hidden from the `FieldGadget` interface
///     and is left for advanced users who want better performance.
///
/// DISCLAIMER: This is entirely a porting of [arkworks/nonnative](https://github.com/arkworks-rs/nonnative)
///             to work with our GingerLib.

/// a submodule for reducing the representations
pub mod reduce;

pub mod nonnative_field_gadget;

pub mod nonnative_field_mul_result_gadget;

#[cfg(test)]
mod tests;

/// a macro for computing ceil(log2(x)) for a field element x
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