use crate::{
    biginteger::BigInteger256 as BigInteger,
    fields::{Fp256, Fp256Parameters, FpParameters},
};

pub type Fr = Fp256<FrParameters>;

pub struct FrParameters;

impl Fp256Parameters for FrParameters {}
impl FpParameters for FrParameters {
    type BigInt = BigInteger;

    // MODULUS = 2^252 + 27742317777372353535851937790883648493.
    const MODULUS: BigInteger = BigInteger([
        0x5812631a5cf5d3ed,
        0x14def9dea2f79cd6,
        0x0000000000000000,
        0x1000000000000000,
    ]);

    const MODULUS_BITS: u32 = 253;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const REPR_SHAVE_BITS: u32 = 3;

    const R: BigInteger = BigInteger([
        0xd6ec31748d98951d,
        0xc6ef5bf4737dcf70,
        0xfffffffffffffffe,
        0xfffffffffffffff,
    ]);

    const R2: BigInteger = BigInteger([
        0xa40611e3449c0f01,
        0xd00e1ba768859347,
        0xceec73d217f5be65,
        0x399411b7c309a3d,
    ]);

    const INV: u64 = 0xd2b51da312547e1b;

    // GENERATOR = 2 (Representend in Montgomery form)
    const GENERATOR: BigInteger = BigInteger([
        0x55c5ffcebe3b564d,
        0x78ffbe0a4404020b,
        0xfffffffffffffffd,
        0xfffffffffffffff,
    ]);

    const TWO_ADICITY: u32 = 2;

    const ROOT_OF_UNITY: BigInteger = BigInteger([
        0x7c790e32b42f0e7d,
        0x4c8ce706a7ae2cc8,
        0xd73823cc921779ad,
        0x5599959893f562a,
    ]);

    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x2c09318d2e7ae9f6,
        0x0a6f7cef517bce6b,
        0x0000000000000000,
        0x800000000000000,
    ]);

    const T: BigInteger = BigInteger([
        0x960498c6973d74fb,
        0x0537be77a8bde735,
        0x0000000000000000,
        0x400000000000000,
    ]);

    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0xcb024c634b9eba7d,
        0x029bdf3bd45ef39a,
        0x0000000000000000,
        0x200000000000000,
    ]);
}
