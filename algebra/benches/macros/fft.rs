macro_rules! basic_domain_fft_bench {
    ($field: ident, $field_ident: ident) => {
        paste::item! {
            #[bench]
            fn [<bench_basic_domain_fft _$field_ident>](b: &mut ::test::Bencher) {
                use rand::SeedableRng;
                use rand_xorshift::XorShiftRng;

                const SAMPLES: usize = 1000;
                let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
            
                let num_coeffs = 1 << 14;
                let domain = algebra::fft::get_best_evaluation_domain::<$field>(num_coeffs).unwrap();
                let domain_size = domain.size();
                assert_eq!(num_coeffs, domain_size);
            
                let v_a: Vec<Vec<$field>> = (0..SAMPLES)
                    .map(|_| {
                        let mut v = vec![];
                        for _ in 0..domain_size {
                            v.push($field::rand(&mut rng));
                        }
                        v
                    })
                    .collect();
            
                let v_b: Vec<Vec<$field>> = (0..SAMPLES)
                    .map(|_| {
                        let mut v = vec![];
                        for _ in 0..domain_size {
                            v.push($field::rand(&mut rng));
                        }
                        v
                    })
                    .collect();
            
                let v_c: Vec<Vec<$field>> = (0..SAMPLES)
                    .map(|_| {
                        let mut v = vec![];
                        for _ in 0..domain_size {
                            v.push($field::rand(&mut rng));
                        }
                        v
                    })
                    .collect();
            
                let mut count = 0;
                b.iter(|| {
                    count = (count + 1) % SAMPLES;
                    let mut a = v_a[count].clone();
                    let mut b = v_b[count].clone();
                    domain.ifft_in_place(&mut a);
                    domain.ifft_in_place(&mut b);
                    domain.coset_fft_in_place(&mut a);
                    domain.coset_fft_in_place(&mut b);
                    let mut ab = domain.mul_polynomials_in_evaluation_domain(&a, &b).unwrap();
                    drop(a);
                    drop(b);
                    let mut c = v_c[count].clone();
                    domain.ifft_in_place(&mut c);
                    domain.coset_fft_in_place(&mut c);
                    domain.divide_by_vanishing_poly_on_coset_in_place(&mut ab);
                    domain.coset_ifft_in_place(&mut ab);
                });
            }
        }
    }   
}


macro_rules! mixed_domain_fft_bench {
    ($field: ident, $field_ident: ident) => {
        paste::item! {
            #[bench]
            fn [<bench_mixed_domain_fft _$field_ident>](b: &mut ::test::Bencher) {
                use rand::SeedableRng;
                use rand_xorshift::XorShiftRng;

                const SAMPLES: usize = 1000;
                let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

                let num_coeffs = 10240;
                let domain = algebra::fft::get_best_evaluation_domain::<$field>(num_coeffs).unwrap();
                let domain_size = domain.size();
                assert_eq!(num_coeffs, domain_size);

                let v_a: Vec<Vec<$field>> = (0..SAMPLES)
                    .map(|_| {
                        let mut v = vec![];
                        for _ in 0..domain_size {
                            v.push($field::rand(&mut rng));
                        }
                        v
                    })
                    .collect();

                let v_b: Vec<Vec<$field>> = (0..SAMPLES)
                    .map(|_| {
                        let mut v = vec![];
                        for _ in 0..domain_size {
                            v.push($field::rand(&mut rng));
                        }
                        v
                    })
                    .collect();

                let v_c: Vec<Vec<$field>> = (0..SAMPLES)
                    .map(|_| {
                        let mut v = vec![];
                        for _ in 0..domain_size {
                            v.push($field::rand(&mut rng));
                        }
                        v
                    })
                    .collect();

                let mut count = 0;
                b.iter(|| {
                    count = (count + 1) % SAMPLES;
                    let mut a = v_a[count].clone();
                    let mut b = v_b[count].clone();
                    domain.ifft_in_place(&mut a);
                    domain.ifft_in_place(&mut b);
                    domain.coset_fft_in_place(&mut a);
                    domain.coset_fft_in_place(&mut b);
                    let mut ab = domain.mul_polynomials_in_evaluation_domain(&a, &b).unwrap();
                    drop(a);
                    drop(b);
                    let mut c = v_c[count].clone();
                    domain.ifft_in_place(&mut c);
                    domain.coset_fft_in_place(&mut c);
                    domain.divide_by_vanishing_poly_on_coset_in_place(&mut ab);
                    domain.coset_ifft_in_place(&mut ab);
                });
            }
        }
    }
}
