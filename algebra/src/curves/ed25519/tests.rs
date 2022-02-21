use crate::curves::tests::edwards_tests;
use crate::{
    curves::{
        ed25519::*,
        models::twisted_edwards_extended::tests::*,
        tests::{curve_tests, sw_jacobian_tests},
        AffineCurve, ProjectiveCurve,
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
        curve_tests::<TEEd25519Projective>();
        edwards_tests::<Ed25519Parameters>()
    }

    #[test]
    fn test_projective_group() {
        let a = rand::random();
        let b = rand::random();
        for _i in 0..100 {
            group_test::<TEEd25519Projective>(a, b);
        }
    }

    #[test]
    fn test_affine_group() {
        let a: TEEd25519Affine = rand::random();
        let b: TEEd25519Affine = rand::random();
        for _i in 0..100 {
            group_test::<TEEd25519Affine>(a, b);
        }
    }

    #[test]
    fn test_generator() {
        let generator = TEEd25519Affine::prime_subgroup_generator();
        assert!(generator.is_valid());
    }

    #[test]
    fn test_conversion() {
        let a: TEEd25519Affine = rand::random();
        let b: TEEd25519Affine = rand::random();
        let a_b = {
            use crate::groups::Group;
            (a + &b).double().double()
        };
        let a_b2 = (a.into_projective() + &b.into_projective())
            .double()
            .double();
        assert_eq!(a_b, a_b2.into_affine());
        assert_eq!(a_b.into_projective(), a_b2);
    }
}

mod short_weierstrass {
    use super::*;
    #[test]
    fn test_projective_curve() {
        curve_tests::<SWEd25519Projective>();
        sw_jacobian_tests::<Ed25519Parameters>()
    }

    #[test]
    fn test_projective_group() {
        let a = rand::random();
        let b = rand::random();
        for _i in 0..100 {
            group_test::<SWEd25519Projective>(a, b);
        }
    }

    #[test]
    fn test_generator() {
        let generator = SWEd25519Affine::prime_subgroup_generator();
        assert!(generator.is_valid());
    }
}

//TODO: Add tests with hardcoded data
