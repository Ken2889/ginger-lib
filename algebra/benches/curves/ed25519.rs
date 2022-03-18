use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use algebra::{
    biginteger::{BigInteger256 as FrRepr, BigInteger256 as FqRepr},
    fields::ed25519::{fq::Fq, fr::Fr},
    BigInteger, Field, PrimeField, Group, Curve, SquareRootField, UniformRand,
};

f_bench!(Fq, Fq, FqRepr, FqRepr, fq);
f_bench!(Fr, Fr, FrRepr, FrRepr, fr);

#[cfg(feature = "fft")]
basic_domain_fft_bench!(Fq, fq);

#[cfg(feature = "fft")]
basic_domain_fft_bench!(Fr, fr);

mod affine_impl {
    use super::*;
    use algebra::curves::ed25519::Ed25519TEExtended;
    ec_bench!(Ed25519TEExtended, ed25519te);
}

mod projective_impl {
    use super::*;
    use algebra::curves::ed25519::Ed25519Jacobian;
    ec_bench!(Ed25519Jacobian, ed25519jacobian);
}

