#![allow(unused_imports, unused_macros)]

use crate::groups::{
    nonnative::short_weierstrass_jacobian::GroupAffineNonNativeGadget,
    test::{group_test_with_incomplete_add, mul_bits_native_test},
};

#[cfg(feature = "tweedle")]
use algebra::fields::tweedle::Fr as TweedleFr;

#[cfg(feature = "bn_382")]
use algebra::fields::bn_382::fr::Fr as BN382Fr;

#[cfg(feature = "ed25519")]
use algebra::{
    curves::ed25519::Ed25519Parameters,
    fields::ed25519::fq::Fq as ed25519Fq,
};

#[cfg(feature = "secp256k1")]
use algebra::{
    curves::secp256k1::Secp256k1Parameters,
    fields::secp256k1::fq::Fq as secp256k1Fq,
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

#[cfg(all(feature = "bn_382", feature = "secp256k1"))]
nonnative_group_test_unsafe_add!(
    Bn382Frsecp256k1Fq,
    1,
    Secp256k1Parameters,
    BN382Fr,
    secp256k1Fq
);

#[cfg(all(feature = "tweedle", feature = "ed25519"))]
nonnative_group_test_unsafe_add!(
    TweedleFred25519Fq,
    1,
    Ed25519Parameters,
    TweedleFr,
    ed25519Fq
);
