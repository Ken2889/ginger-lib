use crate::fields::{
    ed25519::{fq::Fq, fr::Fr},
    tests::{field_test, primefield_test, sqrt_field_test},
};

#[test]
fn test_ed25519_fr() {
    let a: Fr = rand::random();
    let b: Fr = rand::random();
    field_test(a, b);
    primefield_test::<Fr>();
    sqrt_field_test(b);
}

#[test]
fn test_ed25519_fq() {
    let a: Fq = rand::random();
    let b: Fq = rand::random();
    field_test(a, b);
    primefield_test::<Fq>();
    sqrt_field_test(b);
}

//TODO: Add tests with hardcoded data
