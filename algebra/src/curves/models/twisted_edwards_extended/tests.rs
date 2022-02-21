use crate::{fields::Field, MontgomeryModelParameters, SWModelParameters, TEModelParameters};

#[allow(dead_code)]
pub(crate) fn montgomery_conversion_test<P>()
where
    P: TEModelParameters,
{
    // A = 2 * (a + d) / (a - d)
    let a = P::BaseField::one().double()
        * &(P::COEFF_A + &P::COEFF_D)
        * &(P::COEFF_A - &P::COEFF_D).inverse().unwrap();
    // B = 4 / (a - d)
    let b = P::BaseField::one().double().double() * &(P::COEFF_A - &P::COEFF_D).inverse().unwrap();

    assert_eq!(a, P::MontgomeryModelParameters::COEFF_A);
    assert_eq!(b, P::MontgomeryModelParameters::COEFF_B);
}

#[allow(dead_code)]
/// Tests correct Montgomery -> SW conversion.
/// TODO: Would be more correct to include an associated type SWModelParameters to
/// the TEModelParameters or MontgomeryModelParameters trait. We use the workaround
/// below instead for the moment.
pub(crate) fn sw_conversion_test<P>()
where
    P: MontgomeryModelParameters + SWModelParameters,
{
    let three = P::BaseField::from(3u8);
    let nine = three.square();
    let twentyseven = nine * three;
    let a = <P as MontgomeryModelParameters>::COEFF_A;
    let b = <P as MontgomeryModelParameters>::COEFF_B;
    let a_squared = a.square();
    let b_squared = b.square();
    let a_cubed = a_squared * a;
    let b_cubed = b_squared * b;

    // A = (3 - a^2) / 3b^2
    let new_a = (three - a_squared) * ((three * b_squared).inverse().unwrap());

    // B = (2a^3 - 9a)/ 27b^3
    let new_b = (a_cubed.double() - (nine * a)) * ((twentyseven * b_cubed).inverse().unwrap());

    assert_eq!(new_a, <P as SWModelParameters>::COEFF_A);
    assert_eq!(new_b, <P as SWModelParameters>::COEFF_B);
}
