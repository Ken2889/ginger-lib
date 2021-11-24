use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use algebra::{
    biginteger::BigInteger320 as FqRepr,
    fields::secp256k1::fq::Fq,
    BigInteger, Field, PrimeField, SquareRootField, UniformRand,
};

f_bench!(Fq, Fq, FqRepr, FqRepr, fq);