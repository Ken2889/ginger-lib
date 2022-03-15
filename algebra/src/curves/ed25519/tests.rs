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
    fn test_projective_curve() {
        curve_tests::<TEEd25519>();
        edwards_tests::<Ed25519Parameters>()
    }

    #[test]
    fn test_projective_group() {
        let a = rand::random();
        let b = rand::random();
        for _i in 0..100 {
            group_test::<TEEd25519>(a, b);
        }
    }

    #[test]
    fn test_affine_group() {
        let a: TEEd25519 = rand::random();
        let b: TEEd25519 = rand::random();
        for _i in 0..100 {
            group_test::<TEEd25519>(a, b);
        }
    }

    #[test]
    fn test_generator() {
        let generator = TEEd25519::prime_subgroup_generator();
        assert!(generator.is_valid());
    }
}

mod short_weierstrass {
    use super::*;
    #[test]
    fn test_projective_curve() {
        curve_tests::<SWEd25519>();
        sw_jacobian_tests::<Ed25519Parameters>()
    }

    #[test]
    fn test_projective_group() {
        let a = rand::random();
        let b = rand::random();
        for _i in 0..100 {
            group_test::<SWEd25519>(a, b);
        }
    }

    #[test]
    fn test_generator() {
        let generator = SWEd25519::prime_subgroup_generator();
        assert!(generator.is_valid());
    }
}

//TODO: Add tests with hardcoded data
