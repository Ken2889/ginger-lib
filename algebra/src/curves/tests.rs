use crate::{UniformRand, Group};
use crate::{
    curves::Curve,
    fields::{BitIterator, PrimeField},
    serialize::{CanonicalDeserialize, CanonicalSerialize},
    SWModelParameters, /*, TEModelParameters,*/
};
use rand::{thread_rng, SeedableRng};
use rand_xorshift::XorShiftRng;
use std::convert::TryInto;
use std::io::Cursor;
use num_traits::Zero;

pub const ITERATIONS: usize = 10;

fn random_addition_test<G: Curve>() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let a = G::rand(&mut rng);
        let b = G::rand(&mut rng);
        let c = G::rand(&mut rng);
        let a_affine = a.into_affine().unwrap();
        let b_affine = b.into_affine().unwrap();
        let c_affine = c.into_affine().unwrap();

        // a + a should equal the doubling
        {
            let mut aplusa = a;
            aplusa += &a;

            let mut aplusamixed = a;
            aplusamixed.add_assign_affine(&a.into_affine().unwrap());

            let mut adouble = a;
            adouble.double_in_place();

            assert_eq!(aplusa, adouble);
            assert_eq!(aplusa, aplusamixed);
        }

        let mut tmp = vec![G::zero(); 6];

        // (a + b) + c
        tmp[0] = (a + &b) + &c;

        // a + (b + c)
        tmp[1] = a + &(b + &c);

        // (a + c) + b
        tmp[2] = (a + &c) + &b;

        // Mixed addition

        // (a + b) + c
        tmp[3] = G::from_affine(&a_affine);
        tmp[3].add_assign_affine(&b_affine);
        tmp[3].add_assign_affine(&c_affine);

        // a + (b + c)
        tmp[4] = G::from_affine(&b_affine);
        tmp[4].add_assign_affine(&c_affine);
        tmp[4].add_assign_affine(&a_affine);

        // (a + c) + b
        tmp[5] = G::from_affine(&a_affine);
        tmp[5].add_assign_affine(&c_affine);
        tmp[5].add_assign_affine(&b_affine);

        // Comparisons
        for i in 0..6 {
            for j in 0..6 {
                if tmp[i] != tmp[j] {
                    println!("{} \n{}", tmp[i], tmp[j]);
                }
                assert_eq!(tmp[i], tmp[j], "Associativity failed {} {}", i, j);
                assert_eq!(
                    tmp[i].into_affine().unwrap(),
                    tmp[j].into_affine().unwrap(),
                    "Associativity failed"
                );
            }

            assert!(tmp[i] != a);
            assert!(tmp[i] != b);
            assert!(tmp[i] != c);

            assert!(a != tmp[i]);
            assert!(b != tmp[i]);
            assert!(c != tmp[i]);
        }
    }
}

fn random_multiplication_test<G: Curve>() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let mut a = G::rand(&mut rng);
        let mut b = G::rand(&mut rng);
        let a_affine = a.into_affine().unwrap();
        let b_affine = b.into_affine().unwrap();

        let s = G::ScalarField::rand(&mut rng);

        // s ( a + b )
        let mut tmp1 = a;
        tmp1.add_assign(&b);
        tmp1.mul_assign(&s);

        // sa + sb
        a.mul_assign(&s);
        b.mul_assign(&s);

        let mut tmp2 = a;
        tmp2.add_assign(&b);

        // Affine multiplication
        let mut tmp3 = G::mul_bits_affine(&a_affine, BitIterator::new(s.into_repr()));
        tmp3.add_assign(&G::mul_bits_affine(&b_affine, BitIterator::new(s.into_repr())));

        assert_eq!(tmp1, tmp2);
        assert_eq!(tmp1, tmp3);
    }
}

fn random_doubling_test<G: Curve>() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let mut a = G::rand(&mut rng);
        let mut b = G::rand(&mut rng);

        // 2(a + b)
        let mut tmp1 = a;
        tmp1.add_assign(&b);
        tmp1.double_in_place();

        // 2a + 2b
        a.double_in_place();
        b.double_in_place();

        let mut tmp2 = a;
        tmp2.add_assign(&b);

        let mut tmp3 = a;
        tmp3.add_assign_affine(&b.try_into().unwrap());

        assert_eq!(tmp1, tmp2);
        assert_eq!(tmp1, tmp3);
    }
}

fn random_negation_test<G: Curve>() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let r = G::rand(&mut rng);

        let s = G::ScalarField::rand(&mut rng);
        let sneg = -s;
        assert!((s + &sneg).is_zero());

        let mut t1 = r;
        t1.mul_assign(&s);

        let mut t2 = r;
        t2.mul_assign(&sneg);

        let mut t3 = t1;
        t3.add_assign(&t2);
        println!("t3 = {}", t3);
        assert!(t3.is_zero());

        let mut t4 = t1;
        t4.add_assign_affine(&t2.try_into().unwrap());
        assert!(t4.is_zero());

        t1 = -t1;
        assert_eq!(t1, t2);
    }
}

pub fn curve_tests<G: Curve>() {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    // Negation edge case with zero.
    {
        let z = -G::zero();
        assert!(z.is_zero());
    }

    // Doubling edge case with zero.
    {
        let mut z = -G::zero();
        z.double_in_place();
        assert!(z.is_zero());
    }

    // Addition edge cases with zero
    {
        let mut r = G::rand(&mut rng);
        let rcopy = r;
        r.add_assign(&G::zero());
        assert_eq!(r, rcopy);

        let mut z = G::zero();
        z.add_assign(&G::zero());
        assert!(z.is_zero());

        let mut z2 = z;
        z2.add_assign(&r);

        z.add_assign_affine(&r.try_into().unwrap());

        assert_eq!(z, z2);
        assert_eq!(z, r);
    }

    // Transformations
    {
        let a = G::rand(&mut rng);
        let b = G::from_affine(&a.try_into().unwrap());
        let c = G::from_affine(
            &G::from_affine(&a.try_into().unwrap())
                .try_into()
                .unwrap(),
        );
        assert_eq!(a, b);
        assert_eq!(b, c);
    }

    random_addition_test::<G>();
    random_multiplication_test::<G>();
    random_doubling_test::<G>();
    random_negation_test::<G>();
}

pub fn sw_jacobian_tests<P: SWModelParameters>() {
    sw_jacobian_curve_serialization_test::<P>();
    sw_jacobian_random_transformation_test::<P>();
}

pub fn sw_jacobian_curve_serialization_test<P: SWModelParameters>() {
    use crate::curves::models::short_weierstrass_jacobian::Jacobian;

    let buf_size = Jacobian::<P>::zero().serialized_size();

    let rng = &mut thread_rng();

    for _ in 0..ITERATIONS {
        let a = Jacobian::<P>::rand(rng);
        {
            let mut a = a;
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let b = <Jacobian<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap();
            assert_eq!(a, b);
            a.y = -a.y;
            assert_ne!(a, b);
        }

        {
            let mut a = a;
            a.y = -a.y;
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let b = <Jacobian<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap();
            assert_eq!(a, b);
            a.y = -a.y;
            assert_ne!(a, b);
        }

        {
            let a = Jacobian::<P>::zero();
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let b = <Jacobian<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let a = Jacobian::<P>::zero();
            let mut serialized = vec![0; buf_size - 1];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap_err();
        }

        {
            let serialized = vec![0; buf_size - 1];
            let mut cursor = Cursor::new(&serialized[..]);
            <Jacobian<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap_err();
        }

        {
            let mut a = a;
            let mut serialized = vec![0; a.uncompressed_size()];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_uncompressed(&mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let b = Jacobian::<P>::deserialize_uncompressed(&mut cursor).unwrap();
            assert_eq!(a, b);
            a.y = -a.y;
            assert_ne!(a, b);
        }

        {
            let mut a = a;
            a.y = -a.y;
            let mut serialized = vec![0; a.uncompressed_size()];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_uncompressed(&mut cursor).unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let b = Jacobian::<P>::deserialize_uncompressed(&mut cursor).unwrap();
            assert_eq!(a, b);
            a.y = -a.y;
            assert_ne!(a, b);
        }

        {
            let a = Jacobian::<P>::zero();
            let mut serialized = vec![0; a.uncompressed_size()];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_uncompressed(&mut cursor).unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let b = Jacobian::<P>::deserialize_uncompressed(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        // Force deserialize test
        {
            let a = Jacobian::<P>::rand(rng);
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let p1 = <Jacobian<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap();
            let p2 = Jacobian::<P>::force_deserialize(&serialized).unwrap();
            assert_eq!(p1, p2);
        }
    }
}

fn sw_jacobian_random_transformation_test<P: SWModelParameters>() {
    use crate::curves::models::short_weierstrass_jacobian::Jacobian;
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let g = Jacobian::<P>::rand(&mut rng);
        let g_affine = g.try_into().unwrap();
        let g_projective = Jacobian::<P>::from_affine(&g_affine);
        assert_eq!(g, g_projective);
    }

    // Batch normalization
    for _ in 0..10 {
        let mut v = (0..ITERATIONS)
            .map(|_| {
                let mut r = Jacobian::<P>::rand(&mut rng);
                while r.is_normalized() {
                    r.double_in_place();
                }
                r
            })
            .collect::<Vec<_>>();

        for i in &v {
            assert!(!i.is_normalized());
        }

        use rand::distributions::{Distribution, Uniform};
        let between = Uniform::from(0..ITERATIONS);
        // Sprinkle in some normalized points
        for _ in 0..5 {
            v[between.sample(&mut rng)] = Jacobian::<P>::zero();
        }
        for _ in 0..5 {
            let s = between.sample(&mut rng);
            if v[s].is_zero() {
                assert!(v[s].into_affine().is_err());
            } else {
                v[s] = Jacobian::<P>::from_affine(&v[s].into_affine().unwrap());
            }
        }

        let expected_v = v
            .iter()
            .map(|v| {
                if v.is_zero() {
                   Jacobian::<P>::zero()
                } else {
                    Jacobian::<P>::from_affine(&v.into_affine().unwrap())
                }
            })
            .collect::<Vec<_>>();
        Jacobian::<P>::batch_normalization(&mut v);

        for i in &v {
            assert!(i.is_normalized());
        }

        assert_eq!(v, expected_v);
    }
}

pub fn edwards_tests<P: crate::curves::models::TEModelParameters>()
where
    P::BaseField: PrimeField,
{
    edwards_curve_serialization_test::<P>();
    edwards_random_transformation_test::<P>();
}

fn edwards_curve_serialization_test<P: crate::curves::models::TEModelParameters>() {
    use crate::curves::models::twisted_edwards_extended::TEExtended;

    let buf_size = TEExtended::<P>::zero().serialized_size();

    let rng = &mut thread_rng();

    for _ in 0..ITERATIONS {
        let a = TEExtended::<P>::rand(rng);
        {
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let b = <TEExtended<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let a = TEExtended::<P>::zero();
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let b = <TEExtended<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let a = TEExtended::<P>::zero();
            let mut serialized = vec![0; buf_size - 1];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap_err();
        }

        {
            let serialized = vec![0; buf_size - 1];
            let mut cursor = Cursor::new(&serialized[..]);
            <TEExtended<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap_err();
        }

        {
            let mut serialized = vec![0; a.uncompressed_size()];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_uncompressed(&mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let b = TEExtended::<P>::deserialize_uncompressed(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        {
            let a = TEExtended::<P>::zero();
            let mut serialized = vec![0; a.uncompressed_size()];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_uncompressed(&mut cursor).unwrap();
            let mut cursor = Cursor::new(&serialized[..]);
            let b = TEExtended::<P>::deserialize_uncompressed(&mut cursor).unwrap();
            assert_eq!(a, b);
        }

        // Force deserialize test
        {
            let a = TEExtended::<P>::rand(rng);
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            CanonicalSerialize::serialize(&a, &mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let p1 = <TEExtended<P> as CanonicalDeserialize>::deserialize(&mut cursor).unwrap();
            let p2 = TEExtended::<P>::force_deserialize(&serialized).unwrap();
            assert_eq!(p1, p2);
        }
        
    }
}

fn edwards_random_transformation_test<P: crate::curves::models::TEModelParameters>() {
    use crate::curves::models::twisted_edwards_extended::TEExtended;
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let g = TEExtended::<P>::rand(&mut rng);
        let g_affine = g.try_into().unwrap();
        let g_projective = TEExtended::<P>::from_affine(&g_affine);
        assert_eq!(g, g_projective);
    }

    // Batch normalization
    for _ in 0..10 {
        let mut v = (0..ITERATIONS)
            .map(|_| {
                let mut r = TEExtended::<P>::rand(&mut rng);
                while r.is_normalized() {
                    r.double_in_place();
                }
                r
            })
            .collect::<Vec<_>>();

        for i in &v {
            assert!(!i.is_normalized());
        }

        use rand::distributions::{Distribution, Uniform};
        let between = Uniform::from(0..ITERATIONS);
        // Sprinkle in some normalized points
        for _ in 0..5 {
            v[between.sample(&mut rng)] = TEExtended::<P>::zero();
        }
        for _ in 0..5 {
            let s = between.sample(&mut rng);
            v[s] = TEExtended::<P>::from_affine(&v[s].into_affine().unwrap());
        }

        let expected_v = v
            .iter()
            .map(|v| {
                    TEExtended::<P>::from_affine(&v.into_affine().unwrap())
            })
            .collect::<Vec<_>>();
        TEExtended::<P>::batch_normalization(&mut v);

        for i in &v {
            assert!(i.is_normalized());
        }

        assert_eq!(v, expected_v);
    }
}
