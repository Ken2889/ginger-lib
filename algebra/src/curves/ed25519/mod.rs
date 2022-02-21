use crate::{
    biginteger::BigInteger256,
    curves::models::{
        ModelParameters, MontgomeryModelParameters, SWModelParameters, TEModelParameters,
    },
    fields::ed25519::{fq::Fq, fr::Fr},
};
use crate::{field_new, short_weierstrass_jacobian, twisted_edwards_extended};
use std::str::FromStr;

#[cfg(test)]
mod tests;

pub type TEEd25519Affine = twisted_edwards_extended::GroupAffine<Ed25519Parameters>;
pub type TEEd25519Projective = twisted_edwards_extended::GroupProjective<Ed25519Parameters>;
pub type SWEd25519Affine = short_weierstrass_jacobian::GroupAffine<Ed25519Parameters>;
pub type SWEd25519Projective = short_weierstrass_jacobian::GroupProjective<Ed25519Parameters>;

//Generator in the short Weierstrass model
const GENERATOR_X: Fq = field_new!(
    Fq,
    BigInteger256([
        0x08bbc702597f82c2,
        0x32af7b1bfc787efa,
        0xa1b73a6fe2cce7a9,
        0x4df0d058e6887a99,
    ])
);
const GENERATOR_Y: Fq = field_new!(
    Fq,
    BigInteger256([
        0x13d744368a8c51dc,
        0xca98ee7910cd5515,
        0x3eb8da8cc4097750,
        0x336e309b8e6612f0,
    ])
);

// Generator in the Twisted Edwards form
const TE_X: Fq = field_new!(
    Fq,
    BigInteger256([
        0xe2cabc553f9da287,
        0x9ca598562396e489,
        0x9879936bade4b5b7,
        0x759e23707e6077d0,
    ])
);
const TE_Y: Fq = field_new!(
    Fq,
    BigInteger256([
        0x333333333333334a,
        0x3333333333333333,
        0x3333333333333333,
        0x3333333333333333,
    ])
);

/// The curve ed25519 in https://en.wikipedia.org/wiki/EdDSA#Ed25519
/// is a twisted Edwards curve. These curves have equations of the
/// form: ax² + y² = 1 - dx²y².
/// over some base finite field Fq.
/// In our case
/// q = 2^255 - 19.
/// a = -1.
/// d = (121665/121666) mod q
///
/// The curve is isomorphic over GF(q) to the Montgomery curve
///      sqrt(236841848896)·y² = x³ + 486662·x² + x
/// via the equivalence described here:
/// https://en.wikipedia.org/wiki/Montgomery_curve#Equivalence_with_twisted_Edwards_curves    
///
/// Recall that any Montgomery curve B·y² = x³ + A·x² + x
/// is equivalent to a Weierstrass curve via the isomorphism describe here:
/// https://en.wikipedia.org/wiki/Montgomery_curve#Equivalence_with_Weierstrass_curves

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct Ed25519Parameters;

impl ModelParameters for Ed25519Parameters {
    type BaseField = Fq;
    type ScalarField = Fr;
}

impl TEModelParameters for Ed25519Parameters {
    /// COEFF_A = -1
    const COEFF_A: Fq = field_new!(
        Fq,
        BigInteger256([
            0xffffffffffffffc7,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0x7fffffffffffffff,
        ])
    );

    /// COEFF_D = 0x2c822b5a729fc526e5939207bc18869010a18777afc6297380ed8bfedf47e9fa
    const COEFF_D: Fq = field_new!(
        Fq,
        BigInteger256([
            0x80ed8bfedf47e9fa,
            0x10a18777afc62973,
            0xe5939207bc188690,
            0x2c822b5a729fc526,
        ])
    );

    /// COFACTOR = 8
    const COFACTOR: &'static [u64] = &[8];

    /// COFACTOR^(-1) mod r =
    /// 819310549611346726241370945440405716213240158234039660170669895299022906775
    const COFACTOR_INV: Fr = field_new!(
        Fr,
        BigInteger256([
            0xa7ed9ce5a30a2c13,
            0xeb2106215d086329,
            0xffffffffffffffff,
            0xfffffffffffffff,
        ])
    );

    /// AFFINE_GENERATOR_COEFFS = (GENERATOR_X, GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) = (TE_X, TE_Y);

    type MontgomeryModelParameters = Ed25519Parameters;

    /// Multiplication by `a` is simply negation here.
    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        -(*elem)
    }
}

impl MontgomeryModelParameters for Ed25519Parameters {
    /// COEFF_A = 0x76d06
    const COEFF_A: Fq = field_new!(Fq, BigInteger256([0x11a2ee4, 0x0, 0x0, 0x0,]));
    /// COEFF_B = 0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff892e5
    const COEFF_B: Fq = field_new!(
        Fq,
        BigInteger256([
            0xfffffffffee5d0bd,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0x7fffffffffffffff,
        ])
    );

    type TEModelParameters = Ed25519Parameters;
}

impl SWModelParameters for Ed25519Parameters {
    /// COEFF_A = 0
    const COEFF_A: Fq = field_new!(
        Fq,
        BigInteger256([
            0x98e77b38ebeb72af,
            0xfd6b11cfe08460c3,
            0x5c8b67fc784b2dd3,
            0x59ada76a9992562b,
        ])
    );

    /// COEFF_B = 5
    const COEFF_B: Fq = field_new!(
        Fq,
        BigInteger256([
            0x60bafeca20f284f0,
            0x68b75c79f9b5ef81,
            0xa00e82e66cfd1fc2,
            0x50a08320d8fab34c,
        ])
    );

    /// COFACTOR = 1
    const COFACTOR: &'static [u64] = &[0x8];

    /// COFACTOR_INV = 1
    const COFACTOR_INV: Fr = field_new!(
        Fr,
        BigInteger256([
            0xa7ed9ce5a30a2c13,
            0xeb2106215d086329,
            0xffffffffffffffff,
            0xfffffffffffffff,
        ])
    );

    /// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) = (GENERATOR_X, GENERATOR_Y);
}

impl FromStr for TEEd25519Affine {
    type Err = ();

    fn from_str(mut s: &str) -> Result<Self, Self::Err> {
        s = s.trim();
        if s.is_empty() {
            return Err(());
        }
        if s.len() < 3 {
            return Err(());
        }
        if !(s.starts_with('(') && s.ends_with(')')) {
            return Err(());
        }
        let mut point = Vec::new();
        for substr in s.split(|c| c == '(' || c == ')' || c == ',' || c == ' ') {
            if !substr.is_empty() {
                point.push(Fq::from_str(substr)?);
            }
        }
        if point.len() != 2 {
            return Err(());
        }
        let point = TEEd25519Affine::new(point[0], point[1]);

        if !point.is_on_curve() {
            Err(())
        } else {
            Ok(point)
        }
    }
}
