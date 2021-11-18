use crate::groups::{
    nonnative::short_weierstrass_jacobian::GroupAffineNonNativeGadget,
    test::{group_test_with_incomplete_add, mul_bits_native_test},
};
use algebra::{
    curves::secp256k1::Secp256k1Parameters,
    fields::{bn_382::Fr as BN382Fr, secp256k1::Fq as secp256k1Fq},
};

macro_rules! nonnative_test_individual {
    ($test_method:ident, $test_name:ident, $num_samples:expr, $group_params:ty, $test_constraint_field:ty, $test_simulation_field:ty) => {
        paste::item! {
            #[test]
            fn [<$test_method _ $test_name:lower>]() {
                for _ in 0..$num_samples {
                    $test_method::<_, _, GroupAffineNonNativeGadget<$group_params, $test_constraint_field, $test_simulation_field>>();
                }
            }
        }
    };
}

#[allow(unused_macros)]
macro_rules! nonnative_group_test {
    ($test_name:ident, $num_samples:expr, $group_params:ty, $test_constraint_field:ty, $test_simulation_field:ty) => {
        nonnative_test_individual!(
            group_test,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
        nonnative_test_individual!(
            mul_bits_native_test,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
    };
}

macro_rules! nonnative_group_test_unsafe_add {
    ($test_name:ident, $num_samples:expr, $group_params:ty, $test_constraint_field:ty, $test_simulation_field:ty) => {
        nonnative_test_individual!(
            group_test_with_incomplete_add,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
        nonnative_test_individual!(
            mul_bits_native_test,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
    };
}

nonnative_group_test_unsafe_add!(
    Bn382Frsecp256k1Fq,
    1,
    Secp256k1Parameters,
    BN382Fr,
    secp256k1Fq
);
