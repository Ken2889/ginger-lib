//! Base field of JubJub, a 255 bit prime field with duadicity 32.

use crate::{
    biginteger::BigInteger256 as BigInteger,
    fields::{Fp256, Fp256Parameters, FpParameters},
};

pub type Fq = Fp256<FqParameters>;

pub struct FqParameters;

impl Fp256Parameters for FqParameters {}
impl FpParameters for FqParameters {
    type BigInt = BigInteger;

    /// MODULUS =
    /// 5243587517512619047944774050818596583769055250052763782260365869993858\
    /// 1184513
    const MODULUS: BigInteger = BigInteger([
        0xffffffff00000001,
        0x53bda402fffe5bfe,
        0x3339d80809a1d805,
        0x73eda753299d7d48,
    ]);

    const MODULUS_BITS: u32 = 255;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const REPR_SHAVE_BITS: u32 = 1;

    /// Montgomery constant =
    /// 1092033888706381446467550399231597617788887966458528839425026660803596\
    /// 7270910
    const R: BigInteger = BigInteger([
        0x1fffffffe,
        0x5884b7fa00034802,
        0x998c4fefecbc4ff5,
        0x1824b159acc5056f,
    ]);

    /// Montgomery constant squared =
    /// 3294906474794265442129797520630710739278575682199800681788903916070560\
    /// 242797
    const R2: BigInteger = BigInteger([
        0xc999e990f3f29c6d,
        0x2b6cedcb87925c23,
        0x5d314967254398f,
        0x748d9d99f59ff11,
    ]);

    const INV: u64 = 0xfffffffeffffffff;

    /// generator = 7
    const GENERATOR: BigInteger = BigInteger([
        0xefffffff1,
        0x17e363d300189c0f,
        0xff9c57876f8457b0,
        0x351332208fc5a8c4,
    ]);

    const TWO_ADICITY: u32 = 32;

    /// 2^32-th root of unity
    /// 1023822735773949582365103057584923206255886018028447754118950815999128\
    /// 6009131
    const ROOT_OF_UNITY: BigInteger = BigInteger([
        0xb9b58d8c5f0e466a,
        0x5b1b4c801819d7ec,
        0xaf53ae352a31e64,
        0x5bf3adda19e9b27b,
    ]);

    /// (q-)/2 =
    /// 2621793758756309523972387025409298291884527625026381891130182934996929\
    /// 0592256
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x7fffffff80000000,
        0xa9ded2017fff2dff,
        0x199cec0404d0ec02,
        0x39f6d3a994cebea4,
    ]);

    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^S * T

    /// T = (MODULUS - 1) / 2^duadicity =
    /// 12208678567578594777604504606729831043093128246378069236549469339647
    const T: BigInteger = BigInteger([
        0xfffe5bfeffffffff,
        0x9a1d80553bda402,
        0x299d7d483339d808,
        0x73eda753,
    ]);

    /// (T - 1) / 2 =
    /// 6104339283789297388802252303364915521546564123189034618274734669823
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        0x7fff2dff7fffffff,
        0x4d0ec02a9ded201,
        0x94cebea4199cec04,
        0x39f6d3a9,
    ]);
}
