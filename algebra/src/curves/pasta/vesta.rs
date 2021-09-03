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
pub struct PastavestaParameters;

impl ModelParameters for PastavestaParameters {
    type BaseField = Fr;
    type ScalarField = Fq;
}

pub type Affine = GroupAffine<PastavestaParameters>;
pub type Projective = GroupProjective<PastavestaParameters>;

impl SWModelParameters for PastavestaParameters {
    /// COEFF_A = 0
    const COEFF_A: Fq = field_new!(Fq, BigInteger256([0x0, 0x0, 0x0, 0x0, 0x0]));

    /// COEFF_B = 5 (Standard form)
    const COEFF_B: Fq = field_new!(Fq, BigInteger256([
        0x96bc8c8cffffffed, 
        0x74c2a54b49f7778e, 
        0xfffffffffffffffd, 
        0x3fffffffffffffff, 
    ]));

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x1];

    /// COFACTOR_INV = 1
    const COFACTOR_INV: Fr = field_new!(Fr, BigInteger256([
        0x34786d38fffffffd,
        0x992c350be41914ad,
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
/// = 21075379713479047553564266640866527200848352330298207685531992063597154177540
pub const G_GENERATOR_X: Fq = field_new!(Fq, BigInteger256([
    0x690d575717ab0fa1,
    0xe5b0fed1562d521f,
    0x12835922cc9059e7,
    0x2c1073956c933c88,
]));

/// G_GENERATOR_Y =
/// = 22191108764351731276605087184101827634272305989561712051868454664194139283718
pub const G_GENERATOR_Y: Fq = field_new!(Fq, BigInteger256([
    0x027965c57e9640c0,
    0xbbcb566401826342,
    0x76aeacfe1f0bfc9b,
    0x3553f4698b25707a,
]));