use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use algebra::{
    biginteger::{BigInteger320 as FrRepr, BigInteger320 as FqRepr},
    fields::secp256k1::{fq::Fq, fr::Fr},
    curves::secp256k1::Secp256k1Jacobian,
    BigInteger, Field, PrimeField, Group, Curve, SquareRootField, UniformRand,
};

ec_bench!(Secp256k1Jacobian, secp256k1);
f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
f_bench!(Fr, Fr, FrRepr, FrRepr, fr);

#[cfg(feature = "fft")]
basic_domain_fft_bench!(Fq, fq);

#[cfg(feature = "fft")]
basic_domain_fft_bench!(Fr, fr);