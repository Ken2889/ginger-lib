use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use algebra::{
    biginteger::{BigInteger256 as FrRepr, BigInteger256 as FqRepr},
    fields::tweedle::{fq::Fq, fr::Fr},
    curves::tweedle::{dee::DeeJacobian, dum::DumJacobian},
    BigInteger, Field, PrimeField, Group, Curve, SquareRootField, UniformRand,
};

ec_bench!(DeeJacobian, dee);
ec_bench!(DumJacobian, dum);
f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
f_bench!(Fr, Fr, FrRepr, FrRepr, fr);

#[cfg(feature = "fft")]
basic_domain_fft_bench!(Fq, fq);

#[cfg(feature = "fft")]
basic_domain_fft_bench!(Fr, fr);