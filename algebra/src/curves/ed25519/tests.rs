use crate::curves::tests::edwards_tests;
use crate::{
    curves::{
        ed25519::*,
        models::twisted_edwards_extended::tests::*,
        tests::{curve_tests, sw_jacobian_tests},
    },
    groups::tests::group_test,
    SemanticallyValid,
};
use rand;

#[test]
fn test_montgomery_conversion() {
    montgomery_conversion_test::<Ed25519Parameters>();
}

#[test]
fn test_sw_conversion() {
    sw_conversion_test::<Ed25519Parameters>();
}

mod twisted_edwards {
    use super::*;

    #[test]
    fn test_curve() {
        curve_tests::<Ed25519TEExtended>(true);
        edwards_tests::<Ed25519Parameters>()
    }

    #[test]
    fn test_group() {
        let a = rand::random();
        let b = rand::random();
        for _i in 0..100 {
            group_test::<Ed25519TEExtended>(a, b);
        }
    }

    #[test]
    fn test_generator() {
        let generator = Ed25519TEExtended::prime_subgroup_generator();
        assert!(generator.is_valid());
    }
}

mod short_weierstrass {
    use super::*;
    #[test]
    fn test_curve() {
        curve_tests::<Ed25519Jacobian>(true);
        sw_jacobian_tests::<Ed25519Parameters>()
    }

    #[test]
    fn test_group() {
        let a = rand::random();
        let b = rand::random();
        for _i in 0..100 {
            group_test::<Ed25519Jacobian>(a, b);
        }
    }

    #[test]
    fn test_generator() {
        let generator = Ed25519Jacobian::prime_subgroup_generator();
        assert!(generator.is_valid());
    }
}

//TODO: Add tests with hardcoded data
