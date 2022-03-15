use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use algebra::{
    biginteger::{BigInteger256 as FrRepr, BigInteger256 as FqRepr},
    fields::ed25519::{fq::Fq, fr::Fr},
    curves::ed25519::TEEd25519,
    BigInteger, Field, PrimeField, Group, Curve, SquareRootField, UniformRand,
};

ec_bench!(TEEd25519, ed25519);
f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
f_bench!(Fr, Fr, FrRepr, FrRepr, fr);

#[cfg(feature = "fft")]
basic_domain_fft_bench!(Fq, fq);

#[cfg(feature = "fft")]
basic_domain_fft_bench!(Fr, fr);