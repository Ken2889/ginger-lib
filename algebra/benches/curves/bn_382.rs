use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::ops::{AddAssign, MulAssign, SubAssign};

use algebra::{
    fields::bn_382::{
        fq::Fq, fr::Fr,
    },
    // curves::bn_382::{
    //     g1::{Projective as G1, Affine as G1Affine}, g2::{Projective as G2, Affine as G2Affine},
    // },
    biginteger::BigInteger384 as FRepr,
    BigInteger, Field, PrimeField, SquareRootField, UniformRand, ProjectiveCurve
};

//ec_bench!();
f_bench!(Fq, Fq, FRepr, FRepr, fq);
f_bench!(Fr, Fr, FRepr, FRepr, fr);