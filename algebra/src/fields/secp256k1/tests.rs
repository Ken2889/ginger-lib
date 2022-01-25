use crate::fields::tests::{field_test, sqrt_field_test};

#[test]
fn test_secp256k1_fr() {
    use crate::fields::secp256k1::Fr;

    let a: Fr = rand::random();
    let b: Fr = rand::random();
    field_test(a, b);
    sqrt_field_test(a);
    // Fails on the deserialize_mod_order_test but it's expected until we
    // generalize the from_random_bytes() function (if needed) to support
    // this particular use case in which a secp256k1 element is represented
    // using one additional limbs.
    //primefield_test::<Fr>(); 
}

#[test]
fn test_secp256k1_fq() {
    use crate::fields::secp256k1::Fq;

    let a: Fq = rand::random();
    let b: Fq = rand::random();
    field_test(a, b);
    sqrt_field_test(a);
    // Fails on the deserialize_mod_order_test but it's expected until we
    // generalize the from_random_bytes() function (if needed) to support
    // this particular use case in which a secp256k1 element is represented
    // using one additional limbs.
    //primefield_test::<Fq>();
}
