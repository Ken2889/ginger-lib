use crate::{
    biginteger::BigInteger256 as BigInteger,
    fields::{Fp256, Fp256Parameters, FpParameters},
};

pub type Fr = Fp256<FrParameters>;

pub struct FrParameters;

impl Fp256Parameters for FrParameters {}
impl FpParameters for FrParameters {
    type BigInt = BigInteger;
    ///  p = 28948022309329048855892746252171976963363056481941560715954676764349967630337
    const MODULUS: BigInteger = BigInteger([
        0x992d30ed00000001,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ]);

    const MODULUS_BITS: u32 = 255;

    const REPR_SHAVE_BITS: u32 = 1;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const TWO_ADICITY: u32 = 32;

    /// (p-1)/2 = 
    ///  = 14474011154664524427946373126085988481681528240970780357977338382174983815168
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xcc96987680000000,
        0x11234c7e04a67c8d,
        0x0000000000000000,
        0x2000000000000000,
    ]);

    /// T = (MODULUS - 1/2^twoadicity = 
    /// 6739986666787659948666753771754907668419893943225396963757154709741
    const T: BigInteger = BigInteger([
        0x094cf91b992d30ed,
        0x00000000224698fc,
        0x0000000000000000,
        0x40000000,
    ]);

    /// (T - 1) / 2 = 
    /// = 28948022309329048855892746252171976963317496166410141009864396001977208667915
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x04a67c8dcc969876,
        0x0000000011234c7e,
        0x0000000000000000,
        0x20000000,
    ]);

    /// Montgomery constant R = 2^256 mod MODULUS = 
    const R: BigInteger = BigInteger([
        0x34786d38fffffffd,
        0x992c350be41914ad,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ]);

    /// R2 = R^2 mod MODULUS
    const R2: BigInteger = BigInteger([
        0x8c78ecb30000000f,
        0xd7d30dbd8b0de0e7,
        0x7797a99bc3c95d18,
        0x096d41af7b9cb714,
    ]);

    /// INV = -MODULUS^{-1} (mod 2^64)
    const INV: u64 = 0x992d30ecffffffff;

    /// GENERATOR = 5 (Standard repr.)
    /// = 5*R mod MODULUS = - 911206310628394121805615247433704407060 (Montgomery rep.)
    const GENERATOR: BigInteger = BigInteger([
        0xa1a55e68ffffffed,
        0x74c2a54b4f4982f3,
        0xfffffffffffffffd,
        0x3fffffffffffffff,
    ]);

    /// ROOT_OF_UNITY = GENERATOR^T (Montgomery rep.) 
    /// = -1 mod p
    const ROOT_OF_UNITY: BigInteger = BigInteger([
        0xa28db849bad6dbf0,
        0x9083cd03d3b539df,
        0xfba6b9ca9dc8448e,
        0x3ec928747b89c6da,
    ]);

}