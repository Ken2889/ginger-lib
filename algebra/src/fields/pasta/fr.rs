use crate::{
    biginteger::BigInteger256 as BigInteger,
    fields::{Fp256, Fp256Parameters, FpParameters},
};

pub type Fr = Fp256<FrParameters>;

pub struct FrParameters;

impl Fp256Parameters for FrParameters {}
impl FpParameters for FrParameters {
    type BigInt = BigInteger;

    /// p = 28948022309329048855892746252171976963363056481941647379679742748393362948097
    const MODULUS: BigInteger = BigInteger([
        0x8c46eb2100000001,
        0x224698fc0994a8dd,
        0x0000000000000000,
        0x4000000000000000,
    ]);

    const MODULUS_BITS: u32 = 255;

    const REPR_SHAVE_BITS: u32 = 1;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const TWO_ADICITY: u32 = 32;

    /// (p - 1)/2 = 
    /// = 14474011154664524427946373126085988481681528240970823689839871374196681474048
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xc623759080000000,
        0x11234c7e04ca546e,
        0x0000000000000000
        0x2000000000000000,
    ]);
    
    /// T = (p - 1)/2^TWO_ADICITY = 
    /// = 6739986666787659948666753771754907668419893943225417141728043264801
    const T: BigInteger = BigInteger([
        0x0994a8dd8c46eb21,
        0x00000000224698fc,
        0x0000000000000000,
        0x40000000,
    ]);

    /// (T - 1) / 2 = 
    /// = 3369993333393829974333376885877453834209946971612708570864021632400
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x04ca546ec6237590,
        0x0000000011234c7e,
        0x0000000000000000,
        0x20000000,
    ]);

    /// R = 2^256 mod MODULUS = 
    /// = 7976748203231275684456616952498544216114824026705293737984
    const R: BigInteger = BigInteger([
        0x5b2b3e9cfffffffd,
        0x992c350be3420567,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ]);

    /// R2 = (2^256)^2 mod MODULUS
    const R2: BigInteger = BigInteger([
        0xfc9678ff0000000f,
        0x67bb433d891a16e3,
        0x7fae231004ccf590,
        0x096d41af7ccfdaa9,
    ]);

    /// INV = -MODULUS^{-1} (mod 2^64)
    const INV: u64 = 0x8c46eb20ffffffff;

    /// GENERATOR = 5 (Standard rep.)
    /// = - 911206310630127396306934928301610762260 (Montgomery)
    const GENERATOR: BigInteger = BigInteger([
        0x96bc8c8cffffffed,
        0x74c2a54b49f7778e,
        0xfffffffffffffffd,
        0x3fffffffffffffff,
    ]);

    /// ROOT_OF_UNITY = GENERATOR^T (Montgomery rep.)
    const ROOT_OF_UNITY: BigInteger = BigInteger([
        0x218077428c9942de,
        0xcc49578921b60494,
        0xac2e5d27b2efbee2,
        0xb79fa897f2db056,
    ]);

}