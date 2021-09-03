use crate::{Field, field_new};
use crate::biginteger::BigInteger256;
use crate::fields::pasta::{fq::Fq, fr::Fr};
use crate::curves::{
    models::{ModelParameters, SWModelParameters},
    short_weierstrass_jacobian::{GroupAffine, GroupProjective},
};

#[cfg(test)]
mod tests;

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct PastapallasParameters;

impl ModelParameters for PastapallasParameters {
    type BaseField = Fq;
    type ScalarField = Fr;
}

pub type Affine = GroupAffine<PastapallasParameters>;
pub type Projective = GroupProjective<PastapallasParameters>;

impl SWModelParameters for PastapallasParameters {
    /// COEFF_A = 0
    const COEFF_A: Fq = field_new!(Fq, BigInteger256([0x0, 0x0, 0x0, 0x0, 0x0]));

    /// COEFF_B = 5 (Standard form)
    const COEFF_B: Fq = field_new!(Fq, BigInteger256([
        0xa1a55e68ffffffed, 
        0x74c2a54b4f4982f3, 
        0xfffffffffffffffd, 
        0x3fffffffffffffff, 
    ]));

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = 1
    const COFACTOR_INV: Fr = field_new!(Fr, BigInteger256([
        0x5b2b3e9cfffffffd,
        0x992c350be3420567,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ]));

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (G_GENERATOR_X, G_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: &Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }
}

/// G_GENERATOR_X = 
/// = 8080198764325783998360523431226100419341191643195548179194061196794659326913
pub const G_GENERATOR_X: Fq = field_new!(Fq, BigInteger256([
    0xf192ee6b442ee2c3,
    0xb107b24b21b04a36,
    0xc52a7f367412b858,
    0x20cbf7d9078c5bf7,
]));

/// G_GENERATOR_Y =
/// = 32670510020758816978083085130507043184471273380659243275938904335757337482424
pub const G_GENERATOR_Y: Fq = field_new!(Fq, BigInteger256([
    0xfd37b0392c492857,
    0x3c41d285ecb3a5b0,
    0xe22b2ceea39e2f2b,
    0x6e088442e2be966,
]));