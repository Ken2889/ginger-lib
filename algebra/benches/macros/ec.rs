macro_rules! ec_bench {
    ($curve: ident, $curve_ident: ident) => {
        paste::item! {
            #[bench]
            fn [<bench_ $curve_ident _rand>](b: &mut ::test::Bencher) {
                let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
                b.iter(|| $curve::rand(&mut rng));
            }

            #[bench]
            fn [<bench_ $curve_ident _mul_assign>](b: &mut ::test::Bencher) {
                const SAMPLES: usize = 1000;

                let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

                let v: Vec<($curve, <$curve as Group>::ScalarField)> = (0..SAMPLES)
                    .map(|_| ($curve::rand(&mut rng), <$curve as Group>::ScalarField::rand(&mut rng)))
                    .collect();

                let mut count = 0;
                b.iter(|| {
                    let mut tmp = v[count].0;
                    tmp *= &v[count].1;
                    count = (count + 1) % SAMPLES;
                    tmp
                });
            }

            #[bench]
            fn [<bench_ $curve_ident _add_assign>](b: &mut ::test::Bencher) {
                const SAMPLES: usize = 1000;

                let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

                let v: Vec<($curve, $curve)> = (0..SAMPLES)
                    .map(|_| ($curve::rand(&mut rng), $curve::rand(&mut rng)))
                    .collect();

                let mut count = 0;
                b.iter(|| {
                    let mut tmp = v[count].0;
                    n_fold!(tmp, v, add_assign, count);
                    count = (count + 1) % SAMPLES;
                    tmp
                });
            }

            #[bench]
            fn [<bench_ $curve_ident _add_assign_mixed>](b: &mut ::test::Bencher) {
                const SAMPLES: usize = 1000;

                let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

                let v: Vec<($curve, <$curve as Curve>::AffineRep)> = (0..SAMPLES)
                    .map(|_| ($curve::rand(&mut rng), $curve::rand(&mut rng).into_affine().unwrap()))
                    .collect();

                let mut count = 0;
                b.iter(|| {
                    let mut tmp = v[count].0;
                    n_fold!(tmp, v, add_assign_affine, count);
                    count = (count + 1) % SAMPLES;
                    tmp
                });
            }

            #[bench]
            fn [<bench_ $curve_ident _double>](b: &mut ::test::Bencher) {
                const SAMPLES: usize = 1000;

                let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

                let v: Vec<($curve, $curve)> = (0..SAMPLES)
                    .map(|_| ($curve::rand(&mut rng), $curve::rand(&mut rng)))
                    .collect();

                let mut count = 0;
                b.iter(|| {
                    let mut tmp = v[count].0;
                    n_fold!(tmp, double_in_place);
                    count = (count + 1) % SAMPLES;
                    tmp
                });
            }
        }
    };
}
