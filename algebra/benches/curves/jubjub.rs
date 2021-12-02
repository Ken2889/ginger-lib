use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use algebra::{
    biginteger::BigInteger256 as FRepr,
    fields::jubjub::{fq::Fq, fr::Fr},
    BigInteger, Field, PrimeField, SquareRootField, UniformRand,
};

f_bench!(Fq, Fq, FRepr, FRepr, fq);
f_bench!(Fr, Fr, FRepr, FRepr, fr);