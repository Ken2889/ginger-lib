use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use algebra::{
    fields::tweedle::{
        fq::Fq, fr::Fr,
    },
    curves::tweedle::{
        dum::{Projective as G1, Affine as G1Affine}, dee::{Projective as G2, Affine as G2Affine},
    },
    biginteger::BigInteger256 as FRepr,
    BigInteger, Field, PrimeField, SquareRootField, UniformRand, ProjectiveCurve
};

ec_bench!();
f_bench!(Fq, Fq, FRepr, FRepr, fq);
f_bench!(Fr, Fr, FRepr, FRepr, fr);