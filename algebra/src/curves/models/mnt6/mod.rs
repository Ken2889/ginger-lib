use crate::{Fp3, BigInteger768 as BigInteger, PrimeField, SquareRootField, Fp3Parameters,
            Fp6Parameters, SWModelParameters, ModelParameters, PairingEngine, Fp6, PairingCurve,
            Field};
use std::marker::PhantomData;
use std::ops::{Add, Mul, Sub, MulAssign};

pub trait MNT6Parameters: 'static {
    const ATE_LOOP_COUNT: &'static [u64];
    const WNAF: &'static [i32];
    const ATE_IS_LOOP_COUNT_NEG: bool;
    const TWIST: Fp3<Self::Fp3Params>;
    const TWIST_COEFF_A: Fp3<Self::Fp3Params>;
    const FINAL_EXPONENT_LAST_CHUNK_1: BigInteger;
    const FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0: BigInteger;
    const FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG: bool;
    type Fp: PrimeField + SquareRootField + Into<<Self::Fp as PrimeField>::BigInt>;
    type Fp3Params: Fp3Parameters<Fp = Self::Fp>;
    type Fp6Params: Fp6Parameters<Fp3Params = Self::Fp3Params>;
    type G1Parameters: SWModelParameters<BaseField = Self::Fp>;
    type G2Parameters: SWModelParameters<
        BaseField = Fp3<Self::Fp3Params>,
        ScalarField = <Self::G1Parameters as ModelParameters>::ScalarField,
    >;
}

pub mod g1;
pub mod g2;

pub use self::{
    g1::{G1Affine, G1Prepared, G1Projective},
    g2::{G2Affine, G2Prepared, G2Projective},
};
use crate::curves::models::mnt6::g2::G2PreparedCoefficients;

#[derive(Derivative)]
#[derivative(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct MNT6p<P: MNT6Parameters>(PhantomData<fn() -> P>);

impl<P: MNT6Parameters> MNT6p<P> {

    /// Takes as input a point in G1 in projective coordinates, and outputs a
    /// precomputed version of it for pairing purposes.
    fn ate_precompute_g1(value: &G1Affine<P>) -> G1Prepared<P> {
        let mut py_twist_squared = P::TWIST.square();
        py_twist_squared.mul_assign_by_fp(&value.y);

        G1Prepared {p: *value, py_twist_squared}
    }

    /// Takes as input a point in `G2` in projective coordinates, and outputs a
    /// precomputed version of it for pairing purposes.
    fn ate_precompute_g2(value: &G2Affine<P>) -> G2Prepared<P> {

        let mut g2p = G2Prepared {
            q: *value,
            coeffs: vec![],
        };

        let mut s = value.clone();

        for &n in P::WNAF.iter().rev() {

            //Doubling step
            let gamma = {
                let sx_squared = s.x.square();
                let three_sx_squared_plus_a = sx_squared.double().add(&sx_squared).add(&P::TWIST_COEFF_A);
                let two_sy_inv = s.y.double().inverse().unwrap();
                three_sx_squared_plus_a.mul(&two_sy_inv)
            };
            let gamma_x = gamma.mul(&s.x);
            let new_sx = {
                let two_sx = s.x.double();
                gamma.square().sub(&two_sx)
            };
            let new_sy = {
                let sx_minus_new_sx = s.x.sub(&new_sx);
                gamma.mul(&sx_minus_new_sx).sub(&s.y)
            };
            let c = G2PreparedCoefficients{r_y: s.y, gamma, gamma_x};
            g2p.coeffs.push(c);
            s.x = new_sx;
            s.y = new_sy;

            if n != 0 {
                //Addition step
                let sx_minus_x_inv = s.x.sub(&value.x).inverse().unwrap();
                let numerator = if n > 0  { s.y.sub(&value.y) } else { s.y.add(&value.y) };
                let gamma = numerator.mul(&sx_minus_x_inv);
                let gamma_x = gamma.mul(&value.x);
                let new_sx = {
                    let sx_plus_x = s.x.add(&value.x);
                    gamma.square().sub(&sx_plus_x)
                };
                let new_sy = {
                    let sx_minus_new_sx = s.x.sub(&new_sx);
                    gamma.mul(&sx_minus_new_sx).sub(&s.y)
                };
                let c = G2PreparedCoefficients{r_y: s.y, gamma, gamma_x};
                g2p.coeffs.push(c);
                s.x = new_sx;
                s.y = new_sy;
            }
        }
        g2p
    }


    pub fn ate_miller_loop(p: &G1Prepared<P>, q: &G2Prepared<P>) -> Fp6<P::Fp6Params> {

        let mut f = Fp6::<P::Fp6Params>::one();

        let mut idx: usize = 0;


        for &n in P::WNAF.iter().rev() {
            // code below gets executed for all bits (EXCEPT the MSB itself) of
            // mnt4_param_p (skipping leading zeros) in MSB to LSB order

            f = f.square();
            let c = &q.coeffs[idx];
            idx += 1;

            let mut gamma_twist_times_x = c.gamma.mul(&P::TWIST);
            gamma_twist_times_x.mul_assign_by_fp(&p.p.x);
            let g_rr_at_p = Fp6::<P::Fp6Params>::new(
                p.py_twist_squared,
                c.gamma_x - &gamma_twist_times_x  -&c.r_y,
            );

            f = f.mul_by_2345(&g_rr_at_p);

            if n != 0 {
                let c = &q.coeffs[idx];
                idx += 1;

                let mut gamma_twist_times_x = c.gamma.mul(&P::TWIST);
                gamma_twist_times_x.mul_assign_by_fp(&p.p.x);
                let g_rq_at_p_c1 = if n > 0 {
                    c.gamma_x - &gamma_twist_times_x - &q.q.y
                } else {
                    c.gamma_x - &gamma_twist_times_x + &q.q.y
                };
                let g_rq_at_p = Fp6::<P::Fp6Params>::new(
                    p.py_twist_squared,
                    g_rq_at_p_c1,
                );
                f = f.mul_by_2345(&g_rq_at_p);
            }
        }

        if P::ATE_IS_LOOP_COUNT_NEG {
            f = f.unitary_inverse();
        }

        f
    }

    pub fn final_exponentiation(value: &Fp6<P::Fp6Params>) -> Fp6<P::Fp6Params> {
        let value_inv = value.inverse().unwrap();
        let value_to_first_chunk = Self::final_exponentiation_first_chunk(value, &value_inv);
        let value_inv_to_first_chunk = Self::final_exponentiation_first_chunk(&value_inv, value);
        Self::final_exponentiation_last_chunk(&value_to_first_chunk, &value_inv_to_first_chunk)
    }

    fn final_exponentiation_first_chunk(elt: &Fp6<P::Fp6Params>, elt_inv: &Fp6<P::Fp6Params>) -> Fp6<P::Fp6Params> {

        let mut elt_q3 = elt.clone();
        elt_q3.frobenius_map(3);
        let mut elt_q3_over_elt = elt_q3 * &elt_inv;
        let elt_q3_over_elt_clone = elt_q3_over_elt.clone();
        elt_q3_over_elt.frobenius_map(1);
        elt_q3_over_elt.mul_assign(&elt_q3_over_elt_clone);
        elt_q3_over_elt
    }

    fn final_exponentiation_last_chunk(elt: &Fp6<P::Fp6Params>, elt_inv: &Fp6<P::Fp6Params>) -> Fp6<P::Fp6Params> {
        let elt_clone = elt.clone();
        let elt_inv_clone = elt_inv.clone();

        let mut elt_q = elt.clone();
        elt_q.frobenius_map(1);

        let w1_part = elt_q.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_1);
        let w0_part;
        if P::FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG {
            w0_part = elt_inv_clone.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0);
        } else {
            w0_part = elt_clone.cyclotomic_exp(&P::FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0);
        }

        w1_part * &w0_part
    }
}

impl<P: MNT6Parameters> PairingEngine for MNT6p<P>
    where
        G1Affine<P>: PairingCurve<
            BaseField = <P::G1Parameters as ModelParameters>::BaseField,
            ScalarField = <P::G1Parameters as ModelParameters>::ScalarField,
            Projective = G1Projective<P>,
            PairWith = G2Affine<P>,
            Prepared = G1Prepared<P>,
            PairingResult = Fp6<P::Fp6Params>,
        >,
        G2Affine<P>: PairingCurve<
            BaseField = <P::G2Parameters as ModelParameters>::BaseField,
            ScalarField = <P::G1Parameters as ModelParameters>::ScalarField,
            Projective = G2Projective<P>,
            PairWith = G1Affine<P>,
            Prepared = G2Prepared<P>,
            PairingResult = Fp6<P::Fp6Params>,
        >,

{
    type Fr = <P::G1Parameters as ModelParameters>::ScalarField;
    type G1Projective = G1Projective<P>;
    type G1Affine = G1Affine<P>;
    type G2Projective = G2Projective<P>;
    type G2Affine = G2Affine<P>;
    type Fq = P::Fp;
    type Fqe = Fp3<P::Fp3Params>;
    type Fqk = Fp6<P::Fp6Params>;

    fn miller_loop<'a, I>(i: I) -> Self::Fqk
        where
            I: IntoIterator<
                Item = &'a (
                    &'a <Self::G1Affine as PairingCurve>::Prepared,
                    &'a <Self::G2Affine as PairingCurve>::Prepared,
                ),
            >,
    {
        let mut result = Self::Fqk::one();
        for &(ref p, ref q) in i {
            result *= &Self::ate_miller_loop(p, q);
        }
        result
    }

    fn final_exponentiation(r: &Self::Fqk) -> Option<Self::Fqk> {
        Some(Self::final_exponentiation(r))
    }
}
