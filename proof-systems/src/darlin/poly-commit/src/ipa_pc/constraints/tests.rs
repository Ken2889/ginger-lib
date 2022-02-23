use crate::constraints::tests::{
    multi_poly_multi_point_test, single_poly_multi_point_test, test_single_point_multi_poly_verify,
    test_succinct_verify_template,
};
use crate::ipa_pc::constraints::InnerProductArgGadget;
use crate::ipa_pc::InnerProductArgPC;
use algebra::{
    curves::tweedle::dee::{DeeJacobian, TweedledeeParameters},
    fields::tweedle::fq::Fq as tweedleFq,
};
use primitives::TweedleFqPoseidonSponge;
use r1cs_crypto::TweedleFqDensityOptimizedPoseidonSpongeGadget;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::groups::curves::short_weierstrass::AffineGadget;

type ConstraintF = tweedleFq;
type Curve = DeeJacobian;
type CurveGadget = AffineGadget<TweedledeeParameters, ConstraintF, FpGadget<ConstraintF>>;
type FS = TweedleFqPoseidonSponge;
type PC = InnerProductArgPC<Curve, FS>;
type FSG = TweedleFqDensityOptimizedPoseidonSpongeGadget;
type PCG = InnerProductArgGadget<ConstraintF, FSG>;

#[test]
fn test_succinct_verify() {
    test_succinct_verify_template::<ConstraintF, Curve, CurveGadget, PC, PCG>().unwrap()
}

#[test]
fn test_multi_point_succinct_verify() {
    multi_poly_multi_point_test::<ConstraintF, Curve, CurveGadget, PC, PCG>().unwrap()
}

#[test]
fn test_multi_poly_succinct_verify() {
    test_single_point_multi_poly_verify::<ConstraintF, Curve, CurveGadget, PC, PCG>().unwrap()
}

#[test]
fn test_single_poly_multi_point_succinct_verify() {
    single_poly_multi_point_test::<ConstraintF, Curve, CurveGadget, PC, PCG>().unwrap()
}
