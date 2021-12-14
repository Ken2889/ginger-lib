use crate::{
    biginteger::BigInteger256 as BigInteger,
    fields::{Fp256, Fp256Parameters, FpParameters},
};

pub type Fq = Fp256<FqParameters>;

pub struct FqParameters;

impl Fp256Parameters for FqParameters {}
impl FpParameters for FqParameters {
    type BigInt = BigInteger;

    // MODULUS = 2^255 - 19
    const MODULUS: BigInteger = BigInteger([
        0xffffffffffffffed,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0x7fffffffffffffff,
    ]);

    const MODULUS_BITS: u32 = 255;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const REPR_SHAVE_BITS: u32 = 1;

    // R = 2^256 mod MODULUS
    const R: BigInteger = BigInteger([0x26, 0x0, 0x0, 0x0]);

    // R2 = R^2 mod MODULUS
    const R2: BigInteger = BigInteger([0x5a4, 0x0, 0x0, 0x0]);

    // INV = (-MODULUS)^(-1) mod 2^64
    const INV: u64 = 0x86bca1af286bca1b;

    // 2 in Montgomery form
    const GENERATOR: BigInteger = BigInteger([0x4c, 0x0, 0x0, 0x0]);

    const TWO_ADICITY: u32 = 2;

    // 2^((MODULUS -1)/4)
    const ROOT_OF_UNITY: BigInteger = BigInteger([
        0x3b5807d4fe2bdb04,
        0x03f590fdb51be9ed,
        0x6d6e16bf336202d1,
        0x75776b0bd6c71ba8,
    ]);

    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xfffffffffffffff6,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ]);

    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^TWO_ADICITY * T

    // T = (MODULUS - 1) / 2^TWO_ADICITY = 2^253 - 5
    const T: BigInteger = BigInteger([
        0xfffffffffffffffb,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0x1fffffffffffffff,
    ]);

    // (T - 1) / 2 = 2^252 - 3
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xfffffffffffffffd,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xfffffffffffffff,
    ]);
}
