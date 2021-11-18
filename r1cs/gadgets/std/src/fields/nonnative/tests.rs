use crate::{
    alloc::AllocGadget,
    bits::boolean::Boolean,
    eq::EqGadget,
    fields::{
        nonnative::{
            nonnative_field_gadget::NonNativeFieldGadget,
            nonnative_field_mul_result_gadget::NonNativeFieldMulResultGadget,
        },
        FieldGadget,
    },
    test_constraint_system::TestConstraintSystem,
    FromBitsGadget, FromGadget, ToBitsGadget, ToBytesGadget,
};
use algebra::{
    fields::{
        bn_382::{Fq as Bn382Fq, Fr as Bn382Fr},
        secp256k1::Fq as secp256k1Fq,
        tweedle::{Fq as TweedleFq, Fr as TweedleFr},
        FpParameters, PrimeField,
    },
    BigInteger,
};

use r1cs_core::ConstraintSystem;
use rand::{thread_rng, Rng, RngCore};

const NUM_REPETITIONS: usize = 10;
const TEST_COUNT: usize = 10;

fn allocation_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();
    let a_native = SimulationF::rand(rng);
    let a = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc a"), || {
        Ok(a_native)
    })
    .unwrap();

    let a_actual = a.get_value().unwrap();
    let a_expected = a_native;
    assert!(
        a_actual.eq(&a_expected),
        "allocated value does not equal the expected value"
    );

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

fn addition_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let a_native = SimulationF::rand(rng);
    let a = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc a"), || {
        Ok(a_native)
    })
    .unwrap();

    let b_native = SimulationF::rand(rng);
    let b = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc b"), || {
        Ok(b_native)
    })
    .unwrap();

    let a_plus_b = a.add(cs.ns(|| "a + b"), &b).unwrap();

    let a_plus_b_actual = a_plus_b.get_value().unwrap();
    let a_plus_b_expected = a_native + &b_native;
    assert!(a_plus_b_actual.eq(&a_plus_b_expected), "a + b failed");

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

fn multiplication_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();
    let a_native = SimulationF::rand(rng);
    let a = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc a"), || {
        Ok(a_native)
    })
    .unwrap();

    let b_native = SimulationF::rand(rng);
    let b = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc b"), || {
        Ok(b_native)
    })
    .unwrap();

    let a_times_b = a.mul(cs.ns(|| "a * b"), &b).unwrap();

    let a_times_b_actual = a_times_b.get_value().unwrap();
    let a_times_b_expected = a_native * &b_native;

    assert!(
        a_times_b_actual.eq(&a_times_b_expected),
        "a_times_b = {:?}, a_times_b_actual = {:?}, a_times_b_expected = {:?}",
        a_times_b,
        a_times_b_actual.into_repr().as_ref(),
        a_times_b_expected.into_repr().as_ref()
    );

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Checks the `mul` of two randomly sampled non-natives against the expected
/// value as NonNativeFieldGadget in reduced form.
fn equality_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let a_native = SimulationF::rand(rng);
    let a = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc a"), || {
        Ok(a_native)
    })
    .unwrap();

    let b_native = SimulationF::rand(rng);
    let b = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc b"), || {
        Ok(b_native)
    })
    .unwrap();

    let a_times_b = a.mul(cs.ns(|| "a * b"), &b).unwrap();

    let a_times_b_expected = a_native * &b_native;
    let a_times_b_expected_gadget =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc a * b"), || {
            Ok(a_times_b_expected)
        })
        .unwrap();

    a_times_b
        .enforce_equal(cs.ns(|| "expected == actual"), &a_times_b_expected_gadget)
        .unwrap();

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests all combinations of `add` and `mul` of a randomly sampled non-native
/// with the neutral elements of non-native field arithmetics.
fn edge_cases_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let zero_native = SimulationF::zero();
    let zero =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::zero(cs.ns(|| "alloc zero")).unwrap();
    let one = NonNativeFieldGadget::<SimulationF, ConstraintF>::one(cs.ns(|| "alloc one")).unwrap();

    let a_native = SimulationF::rand(rng);
    let minus_a_native = SimulationF::zero() - &a_native;
    let a = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc a"), || {
        Ok(a_native)
    })
    .unwrap();

    let a_plus_zero = a.add(cs.ns(|| "a + 0"), &zero).unwrap();
    let a_minus_zero = a.sub(cs.ns(|| "a - 0"), &zero).unwrap();
    let zero_minus_a = zero.sub(cs.ns(|| "0 - a"), &a).unwrap();
    let a_times_zero = a.mul(cs.ns(|| "a * 0"), &zero).unwrap();

    let zero_plus_a = zero.add(cs.ns(|| "0 + a"), &a).unwrap();
    let zero_times_a = zero.mul(cs.ns(|| "0 * a"), &a).unwrap();

    let a_times_one = a.mul(cs.ns(|| "a * 1"), &one).unwrap();
    let one_times_a = one.mul(cs.ns(|| "1 * a"), &a).unwrap();

    let a_plus_zero_native = a_plus_zero.get_value().unwrap();
    let a_minus_zero_native = a_minus_zero.get_value().unwrap();
    let zero_minus_a_native = zero_minus_a.get_value().unwrap();
    let a_times_zero_native = a_times_zero.get_value().unwrap();
    let zero_plus_a_native = zero_plus_a.get_value().unwrap();
    let zero_times_a_native = zero_times_a.get_value().unwrap();
    let a_times_one_native = a_times_one.get_value().unwrap();
    let one_times_a_native = one_times_a.get_value().unwrap();

    assert!(
        a_plus_zero_native.eq(&a_native),
        "a_plus_zero = {:?}, a = {:?}",
        a_plus_zero_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );
    assert!(
        a_minus_zero_native.eq(&a_native),
        "a_minus_zero = {:?}, a = {:?}",
        a_minus_zero_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );
    assert!(
        zero_minus_a_native.eq(&minus_a_native),
        "zero_minus_a = {:?}, minus_a = {:?}",
        zero_minus_a_native.into_repr().as_ref(),
        minus_a_native.into_repr().as_ref()
    );
    assert!(
        a_times_zero_native.eq(&zero_native),
        "a_times_zero = {:?}, zero = {:?}",
        a_times_zero_native.into_repr().as_ref(),
        zero_native.into_repr().as_ref()
    );
    assert!(
        zero_plus_a_native.eq(&a_native),
        "zero_plus_a = {:?}, a = {:?}",
        zero_plus_a_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );
    assert!(
        zero_times_a_native.eq(&zero_native),
        "zero_times_a = {:?}, zero = {:?}",
        zero_times_a_native.into_repr().as_ref(),
        zero_native.into_repr().as_ref()
    );
    assert!(
        a_times_one_native.eq(&a_native),
        "a_times_one = {:?}, a = {:?}",
        a_times_one_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );
    assert!(
        one_times_a_native.eq(&a_native),
        "one_times_a = {:?}, a = {:?}",
        one_times_a_native.into_repr().as_ref(),
        a_native.into_repr().as_ref()
    );

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Checks the validity of the distributive law `(a+b)*c= a*c + b*c` on randomly
/// sampled `a`, `b`, and `c`.
fn distribution_law_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(
    rng: &mut R,
) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();
    let a_native = SimulationF::rand(rng);
    let b_native = SimulationF::rand(rng);
    let c_native = SimulationF::rand(rng);

    let a_plus_b_native = a_native + &b_native;
    let a_times_c_native = a_native * &c_native;
    let b_times_c_native = b_native * &c_native;
    let a_plus_b_times_c_native = a_plus_b_native * &c_native;
    let a_times_c_plus_b_times_c_native = a_times_c_native + &b_times_c_native;

    assert!(
        a_plus_b_times_c_native.eq(&a_times_c_plus_b_times_c_native),
        "(a + b) * c doesn't equal (a * c) + (b * c)"
    );

    let a = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "a"), || Ok(a_native))
        .unwrap();
    let b = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "b"), || Ok(b_native))
        .unwrap();
    let c = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "c"), || Ok(c_native))
        .unwrap();

    let a_plus_b = a.add(cs.ns(|| "a + b"), &b).unwrap();
    let a_times_c = a.mul(cs.ns(|| "a * c"), &c).unwrap();
    let b_times_c = b.mul(cs.ns(|| "b * c"), &c).unwrap();
    let a_plus_b_times_c = a_plus_b.mul(cs.ns(|| "(a + b) * c"), &c).unwrap();
    let a_times_c_plus_b_times_c = a_times_c.add(cs.ns(|| "ac + bc"), &b_times_c).unwrap();

    assert!(
        a_plus_b.get_value().unwrap().eq(&a_plus_b_native),
        "a + b doesn't match"
    );
    assert!(
        a_times_c.get_value().unwrap().eq(&a_times_c_native),
        "a * c doesn't match"
    );
    assert!(
        b_times_c.get_value().unwrap().eq(&b_times_c_native),
        "b * c doesn't match"
    );
    assert!(
        a_plus_b_times_c
            .get_value()
            .unwrap()
            .eq(&a_plus_b_times_c_native),
        "(a + b) * c doesn't match"
    );
    assert!(
        a_times_c_plus_b_times_c
            .get_value()
            .unwrap()
            .eq(&a_times_c_plus_b_times_c_native),
        "(a * c) + (b * c) doesn't match"
    );
    assert!(
        a_plus_b_times_c_native.eq(&a_times_c_plus_b_times_c_native),
        "(a + b) * c != (a * c) + (b * c)"
    );
    assert!(cs.is_satisfied());
    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
}

/// Tests correctness of `add_in_place`, `sub_in_place` and `mul_in_place` on randomly sampled
/// non-natives.
fn randomized_arithmetic_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(
    rng: &mut R,
) {
    use rand::prelude::SliceRandom;

    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    // Sample random operations to perform
    let mut operations = (0..=2)
        .flat_map(|op| vec![op; TEST_COUNT])
        .collect::<Vec<_>>();
    operations.shuffle(rng);

    let mut num_native = SimulationF::rand(rng);
    let mut num =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "initial num"), || {
            Ok(num_native)
        })
        .unwrap();
    for (i, op) in operations.iter().enumerate() {
        let next_native = SimulationF::rand(rng);
        let next = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("next num for repetition {}", i)),
            || Ok(next_native),
        )
        .unwrap();
        match op {
            0 => {
                num_native += &next_native;
                num.add_in_place(cs.ns(|| format!("num += next {}", i)), &next)
                    .unwrap();
            }
            1 => {
                num_native *= &next_native;
                num.mul_in_place(cs.ns(|| format!("num *= next {}", i)), &next)
                    .unwrap();
            }
            2 => {
                num_native -= &next_native;
                num.sub_in_place(cs.ns(|| format!("num -= next {}", i)), &next)
                    .unwrap();
            }
            _ => (),
        };

        assert!(
            num.get_value().unwrap().eq(&num_native),
            "randomized arithmetic failed:"
        );
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests correctness of `TEST_COUNT` many `add_in_place` on a random instance.
fn addition_stress_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let mut num_native = SimulationF::rand(rng);
    let mut num = NonNativeFieldGadget::alloc(cs.ns(|| "initial num"), || Ok(num_native)).unwrap();
    for i in 0..TEST_COUNT {
        let next_native = SimulationF::rand(rng);
        let next = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("next num for repetition {}", i)),
            || Ok(next_native),
        )
        .unwrap();
        num_native += &next_native;
        num.add_in_place(cs.ns(|| format!("num += next {}", i)), &next)
            .unwrap();

        assert!(num.get_value().unwrap().eq(&num_native));
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests correctness of `TEST_COUNT` many `mul_in_place` on a random instance.
fn multiplication_stress_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(
    rng: &mut R,
) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let mut num_native = SimulationF::rand(rng);
    let mut num =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "initial num"), || {
            Ok(num_native)
        })
        .unwrap();
    for i in 0..TEST_COUNT {
        let next_native = SimulationF::rand(rng);
        let next = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("next num for repetition {}", i)),
            || Ok(next_native),
        )
        .unwrap();
        num_native *= &next_native;
        num.mul_in_place(cs.ns(|| format!("num *= next {}", i)), &next)
            .unwrap();

        assert!(num.get_value().unwrap().eq(&num_native));
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests correctness of `TEST_COUNT` many steps of the randomized recursion
/// `x <- b*x + a`, starting with a random non-native `x`.
fn mul_and_add_stress_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(
    rng: &mut R,
) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let mut num_native = SimulationF::rand(rng);
    let mut num =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "initial num"), || {
            Ok(num_native)
        })
        .unwrap();
    for i in 0..TEST_COUNT {
        let next_add_native = SimulationF::rand(rng);
        let next_add = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("next to add num for repetition {}", i)),
            || Ok(next_add_native),
        )
        .unwrap();
        let next_mul_native = SimulationF::rand(rng);
        let next_mul = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("next to mul num for repetition {}", i)),
            || Ok(next_mul_native),
        )
        .unwrap();

        num_native = num_native * &next_mul_native + &next_add_native;
        num = num
            .mul(cs.ns(|| format!("num * next_mul {}", i)), &next_mul)
            .unwrap()
            .add(
                cs.ns(|| format!("num * next_mul + next_add {}", i)),
                &next_add,
            )
            .unwrap();

        assert!(num.get_value().unwrap().eq(&num_native));
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests correctness of `TEST_COUNT` many steps of the randomized recursion
/// `x <- x*x*b + a`, starting with a random non-native `x`.
fn square_mul_add_stress_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(
    rng: &mut R,
) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let mut num_native = SimulationF::rand(rng);
    let mut num =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "initial num"), || {
            Ok(num_native)
        })
        .unwrap();
    for i in 0..TEST_COUNT {
        let next_add_native = SimulationF::rand(rng);
        let next_add = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("next to add num for repetition {}", i)),
            || Ok(next_add_native),
        )
        .unwrap();
        let next_mul_native = SimulationF::rand(rng);
        let next_mul = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("next to mul num for repetition {}", i)),
            || Ok(next_mul_native),
        )
        .unwrap();

        num_native = num_native * &num_native * &next_mul_native + &next_add_native;
        num = num
            .mul(cs.ns(|| format!("num * num {}", i)), &num)
            .unwrap()
            .mul(cs.ns(|| format!("num * num * next_mul {}", i)), &next_mul)
            .unwrap()
            .add(
                cs.ns(|| format!("num * num* next_mul + next_add {}", i)),
                &next_add,
            )
            .unwrap();

        assert!(num.get_value().unwrap().eq(&num_native));
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests correctness of `TEST_COUNT + ConstraintF::size_in_bits()` many steps of the recursion
/// `x <- (x+x)*(x+x)`, starting with a random non-native `x`.
fn double_stress_test_1<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let mut num_native = SimulationF::rand(rng);
    let mut num =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "initial num"), || {
            Ok(num_native)
        })
        .unwrap();
    // Add to at least ConstraintF::size_in_bits() to ensure that we treat the overflowing
    for i in 0..TEST_COUNT + ConstraintF::size_in_bits() {
        // double
        num_native = num_native + &num_native;
        num = num.add(cs.ns(|| format!("num + num {}", i)), &num).unwrap();

        assert!(num.get_value().unwrap().eq(&num_native), "result incorrect");
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests correctness of `TEST_COUNT` many steps of the recursion
/// `x <- (x+x)*(x+x)`, starting with a random non-native `x`.
fn double_stress_test_2<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let mut num_native = SimulationF::rand(rng);
    let mut num =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "initial num"), || {
            Ok(num_native)
        })
        .unwrap();
    for i in 0..TEST_COUNT {
        // double
        num_native = num_native + &num_native;
        num = num.add(cs.ns(|| format!("num + num {}", i)), &num).unwrap();

        assert!(num.get_value().unwrap().eq(&num_native));

        // square
        let num_square_native = num_native * &num_native;
        let num_square = num.mul(cs.ns(|| format!("num * num {}", i)), &num).unwrap();
        assert!(num_square.get_value().unwrap().eq(&num_square_native));
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests correctness of `TEST_COUNT` many steps of the recursion
/// `x <- (x+x)*(x+x)`, starting with a random non-native `x`.  
fn double_stress_test_3<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let mut num_native = SimulationF::rand(rng);
    let mut num =
        NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "initial num"), || {
            Ok(num_native)
        })
        .unwrap();
    for i in 0..TEST_COUNT {
        // double
        num_native = num_native + &num_native;
        num = num.add(cs.ns(|| format!("num + num {}", i)), &num).unwrap();

        assert!(num.get_value().unwrap().eq(&num_native));

        // square
        let num_square_native = num_native * &num_native;
        let num_square = num.mul(cs.ns(|| format!("num * num {}", i)), &num).unwrap();
        let num_square_native_gadget = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("repetition: alloc_native num {}", i)),
            || Ok(num_square_native),
        )
        .unwrap();

        num_square
            .enforce_equal(
                cs.ns(|| format!("enforce square {}", i)),
                &num_square_native_gadget,
            )
            .unwrap();
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

/// Tests correctness of inverse on `TEST_COUNT` many random instances.
fn inverse_stress_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    for i in 0..TEST_COUNT {
        let num_native = SimulationF::rand(rng);
        let num = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            cs.ns(|| format!("num {}", i)),
            || Ok(num_native),
        )
        .unwrap();

        if num_native == SimulationF::zero() {
            continue;
        }

        let num_native_inverse = num_native.inverse().unwrap();
        let num_inverse = num.inverse(cs.ns(|| format!("inverse {}", i))).unwrap();

        assert!(num_inverse.get_value().unwrap().eq(&num_native_inverse));
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

fn even_odd_stress_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: RngCore>(rng: &mut R) {
    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let one = NonNativeFieldGadget::<SimulationF, ConstraintF>::one(cs.ns(|| "one")).unwrap();
    let two = one.double(cs.ns(|| "two")).unwrap();

    assert!(one
        .is_odd(cs.ns(|| "one is odd"))
        .unwrap()
        .get_value()
        .unwrap());
    assert!(!two
        .is_odd(cs.ns(|| "two is not odd"))
        .unwrap()
        .get_value()
        .unwrap());

    for i in 0..TEST_COUNT {
        let mut iter_cs = cs.ns(|| format!("iter_{}", i));

        let random_native = SimulationF::rand(rng);
        let random = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
            iter_cs.ns(|| "alloc random"),
            || Ok(random_native),
        )
        .unwrap();

        assert_eq!(
            random_native.is_odd(),
            random
                .is_odd(iter_cs.ns(|| "is random odd"))
                .unwrap()
                .get_value()
                .unwrap()
        );
    }
    assert!(cs.is_satisfied());
}

/// Test basic correctness of from_bits for NonNativeFieldGadget over TEST_COUNT many random instances.
fn from_bits_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: Rng>(rng: &mut R) {
    let num_bits_modulus = SimulationF::size_in_bits();

    let test_case = |val: SimulationF, val_bits: Vec<bool>, rng: &mut R| {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        let bits =
            Vec::<Boolean>::alloc(cs.ns(|| "alloc val bits"), || Ok(val_bits.as_slice())).unwrap();
        let val_g = NonNativeFieldGadget::<SimulationF, ConstraintF>::from_bits(
            cs.ns(|| "pack bits"),
            bits.as_slice(),
        )
        .unwrap();
        assert_eq!(val, val_g.get_value().unwrap());
        assert!(cs.is_satisfied());

        //Let's alter one random bit and check that the cs is not satisfied anymore
        let random_bit: usize = rng.gen_range(0..bits.len());
        let prev_value = bits[random_bit].get_value().unwrap();
        let new_value = if prev_value {
            ConstraintF::zero()
        } else {
            ConstraintF::one()
        };
        cs.set(
            format!("alloc val bits/value_{}/boolean", random_bit).as_ref(),
            new_value,
        );
        assert!(!cs.is_satisfied());
        // TODO: Compute correct limb expected to fail
        let expected_fail = "pack bits/packing bits to limb".to_string();
        let actual_fail = cs.which_is_unsatisfied().unwrap().to_owned();
        assert!(
            actual_fail.contains(expected_fail.as_str()),
            "Expected {}, Found: {}",
            expected_fail,
            actual_fail
        );
    };

    for _ in 0..TEST_COUNT {
        // Case 1: bits.len() == SimulationF::MODULUS_BITS
        {
            let val = SimulationF::rand(rng);
            test_case(val, val.write_bits(), rng);
        }

        // Case 2: bits.len() < SimulationF::MODULUS_BITS
        {
            let truncate_at = rng.gen_range(1..num_bits_modulus);
            let val_temp = SimulationF::rand(rng);
            let val_bits = (&val_temp.write_bits()[truncate_at..]).to_vec();
            let val = SimulationF::read_bits(val_bits.clone()).unwrap();
            test_case(val, val_bits, rng);
        }

        // Case 3: bits_val >= SimulationF::MODULUS
        {
            // for simplicity, we take the maximum possible value
            let val_bits = vec![true; num_bits_modulus];
            let val = {
                let mut bi = <SimulationF::BigInt as BigInteger>::from_bits(val_bits.as_slice());
                bi.sub_noborrow(&SimulationF::Params::MODULUS);
                SimulationF::from_repr(bi)
            };
            test_case(val, val_bits, rng);
        }
    }
}

fn from_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: Rng>(rng: &mut R) {
    for _ in 0..TEST_COUNT {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        let f = SimulationF::rand(rng);

        let f_var = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc_input(
            cs.ns(|| "alloc input f"),
            || Ok(f),
        )
        .unwrap();
        let f_var_converted: NonNativeFieldMulResultGadget<SimulationF, ConstraintF> =
            FromGadget::from(&f_var, cs.ns(|| "convert f")).unwrap();
        let f_var_converted_reduced = f_var_converted
            .reduce(cs.ns(|| "reduce f_var_converted"))
            .unwrap();

        let f_var_value = f_var.get_value().unwrap();
        let f_var_converted_reduced_value = f_var_converted_reduced.get_value().unwrap();

        assert_eq!(f, f_var_value);
        assert_eq!(f_var_value, f_var_converted_reduced_value);

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
    }
}

fn to_bits_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: Rng>(rng: &mut R) {
    for _ in 0..TEST_COUNT {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();
        let f = SimulationF::rand(rng);
        let f_bits = f.write_bits();

        let f_var = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc_input(
            cs.ns(|| "alloc input f"),
            || Ok(f),
        )
        .unwrap();

        let f_var_bits = f_var
            .to_bits_strict(cs.ns(|| "f to bits strict"))
            .unwrap()
            .into_iter()
            .map(|b| b.get_value().unwrap())
            .collect::<Vec<bool>>();

        assert_eq!(f_bits, f_var_bits);
        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
    }
}

fn to_bytes_test<SimulationF: PrimeField, ConstraintF: PrimeField, R: Rng>(rng: &mut R) {
    use algebra::CanonicalSerialize;

    let mut cs = TestConstraintSystem::<ConstraintF>::new();

    let target_test_elem = SimulationF::from(123456u128);
    let target_test_gadget = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(
        cs.ns(|| "alloc target test gadget"),
        || Ok(target_test_elem),
    )
    .unwrap();

    let target_to_bytes: Vec<u8> = target_test_gadget
        .to_bytes_strict(cs.ns(|| "target_test_gadget to bytes strict"))
        .unwrap()
        .iter()
        .map(|v| v.get_value().unwrap())
        .collect();

    // 123456 = 65536 + 226 * 256 + 64
    assert_eq!(target_to_bytes[0], 64);
    assert_eq!(target_to_bytes[1], 226);
    assert_eq!(target_to_bytes[2], 1);

    for byte in target_to_bytes.iter().skip(3) {
        assert_eq!(*byte, 0);
    }

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());

    for _ in 0..TEST_COUNT {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();
        let f = SimulationF::rand(rng);
        let mut f_bytes = Vec::with_capacity(f.serialized_size());
        CanonicalSerialize::serialize(&f, &mut f_bytes).unwrap();

        let f_var = NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc_input(
            cs.ns(|| "alloc input f"),
            || Ok(f),
        )
        .unwrap();

        let f_var_bytes = f_var
            .to_bytes_strict(cs.ns(|| "f to bytes strict"))
            .unwrap()
            .into_iter()
            .map(|b| b.get_value().unwrap())
            .collect::<Vec<u8>>();

        assert_eq!(f_bytes, f_var_bytes);
        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
    }
}

// Macros for implementing above tests on non-native arithmetics
macro_rules! nonnative_test_individual {
    ($test_method:ident, $test_name:ident, $test_simulation_field:ty, $test_constraint_field:ty) => {
        paste::item! {
            #[test]
            fn [<$test_method _ $test_name:lower>]() {
                let rng = &mut thread_rng();

                for _ in 0..NUM_REPETITIONS {
                    $test_method::<$test_simulation_field, $test_constraint_field, _>(rng);
                }
            }
        }
    };
}

macro_rules! nonnative_test {
    ($test_name:ident, $test_simulation_field:ty, $test_constraint_field:ty) => {
        nonnative_test_individual!(
            allocation_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            addition_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            multiplication_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            equality_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            edge_cases_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            distribution_law_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            addition_stress_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            double_stress_test_1,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            double_stress_test_2,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            double_stress_test_3,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            randomized_arithmetic_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            multiplication_stress_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            mul_and_add_stress_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            square_mul_add_stress_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            inverse_stress_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            even_odd_stress_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            from_bits_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            from_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            to_bits_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
        nonnative_test_individual!(
            to_bytes_test,
            $test_name,
            $test_simulation_field,
            $test_constraint_field
        );
    };
}

// Implementation of the above non-native arithmetic tests for different curves
nonnative_test!(TweedleFqFr, TweedleFq, TweedleFr);
nonnative_test!(TweedleFrFq, TweedleFr, TweedleFq);
nonnative_test!(Bn382FqFr, Bn382Fq, Bn382Fr);
nonnative_test!(Bn382FrFq, Bn382Fr, Bn382Fq);
nonnative_test!(Bn382Frsecp256k1Fq, Bn382Fr, secp256k1Fq);
nonnative_test!(Bn382Fqsecp256k1Fq, Bn382Fq, secp256k1Fq);
nonnative_test!(Bn382FrTweedleFq, Bn382Fr, TweedleFq);
// TODO: This test, along with some others, seems to cause troubles
//       with the enforce_in_field gadget. Fix it.
/*nonnative_test!(
    TweedleFqBn382Fr,
    TweedleFq,
    Bn382Fr
);*/
