use crate::fields::{Field, PrimeField, SquareRootField};

pub mod short_weierstrass_jacobian;
pub mod short_weierstrass_projective;
pub mod twisted_edwards_extended;

pub trait ModelParameters: Send + Sync + 'static {
    type BaseField: Field + SquareRootField;
    type ScalarField: PrimeField + SquareRootField + Into<<Self::ScalarField as PrimeField>::BigInt>;
}

pub trait SWModelParameters: ModelParameters {
    const COEFF_A: Self::BaseField;
    const COEFF_B: Self::BaseField;
    const COFACTOR: &'static [u64];
    const COFACTOR_INV: Self::ScalarField;
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }

    #[inline(always)]
    fn add_b(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy += &Self::COEFF_B;
        copy
    }
}

pub trait TEModelParameters: ModelParameters {
    const COEFF_A: Self::BaseField;
    const COEFF_D: Self::BaseField;
    const COFACTOR: &'static [u64];
    const COFACTOR_INV: Self::ScalarField;
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField);

    type MontgomeryModelParameters: MontgomeryModelParameters<BaseField = Self::BaseField>;

    #[inline(always)]
    fn mul_by_a(elem: &Self::BaseField) -> Self::BaseField {
        let mut copy = *elem;
        copy *= &Self::COEFF_A;
        copy
    }
}

pub trait MontgomeryModelParameters: ModelParameters {
    const COEFF_A: Self::BaseField;
    const COEFF_B: Self::BaseField;

    type TEModelParameters: TEModelParameters<BaseField = Self::BaseField>;
}

/// Parameters for endomorphism-based scalar multiplication [Halo](https://eprint.iacr.org/2019/1021).
pub trait EndoMulParameters: SWModelParameters {
    
    /// A non-trivial cubic root of unity `ENDO_COEFF` for a curve endomorphism of the form
    ///     (x, y) -> (ENDO_COEFF * x, y).
    const ENDO_COEFF: Self::BaseField;

    /// The scalar representation `zeta_r` of `ENDO_COEFF`.
    /// NOTE : If one wants to use the endo mul circuit with `lambda` many bits,
    /// then `zeta_r` MUST satisfy the minimal distance property
    ///     D = min { d(n*zeta_r, m*zeta_r) : n,m in [0, T] } >= R + 1,
    /// where `T = 2^{lambda/2 + 1} + 2^{lambda/2} - 1` is the output
    /// bound for the coefficients a, b of the equivalent scalar
    /// representation `a*zeta_r + b`.
    const ENDO_SCALAR: Self::ScalarField;

    /// Maximum number of bits for which security of endo mul is proven. MUST be an even number.
    const LAMBDA: usize;
}
