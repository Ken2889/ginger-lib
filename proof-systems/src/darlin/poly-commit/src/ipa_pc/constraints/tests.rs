use crate::constraints::tests::{constant_polynomial_succinct_verify_test, multi_poly_multi_point_test, single_point_multi_poly_test, single_poly_multi_point_test, succinct_verify_single_point_single_poly_test, succinct_verify_with_segmentation_test};
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
type PCG = InnerProductArgGadget<ConstraintF, FSG, Curve, CurveGadget>;

#[test]
fn test_succinct_verify() {
    succinct_verify_single_point_single_poly_test::<ConstraintF, Curve, PC, PCG>()
}

#[test]
fn test_succinct_verify_with_segmentation() {
    succinct_verify_with_segmentation_test::<ConstraintF, Curve, PC, PCG>()
}

#[test]
fn test_multi_point_succinct_verify() {
    multi_poly_multi_point_test::<ConstraintF, Curve, PC, PCG>()
}

#[test]
fn test_single_point_multi_poly_succinct_verify() {
    single_point_multi_poly_test::<ConstraintF, Curve, PC, PCG>()
}



#[test]
fn test_single_poly_multi_point_succinct_verify() {
    single_poly_multi_point_test::<ConstraintF, Curve, PC, PCG>()
}

#[test]
fn test_constant_polynomial_succinct_verify() {
    constant_polynomial_succinct_verify_test::<ConstraintF, Curve, PC, PCG>()
}
