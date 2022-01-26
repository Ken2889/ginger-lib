use algebra::{
    curves::models::{SWModelParameters, TEModelParameters},
    PrimeField, FpParameters,
};

use crate::{fields::fp::FpGadget, uint8::UInt8, boolean::Boolean, FromBitsGadget};
use crate::{
    fields::FieldGadget,
    groups::curves::short_weierstrass::{
        short_weierstrass_jacobian::AffineGadget as SWJAffineGadget,
        short_weierstrass_projective::AffineGadget as SWPAffineGadget,
    },
    groups::curves::twisted_edwards::AffineGadget as TEAffineGadget,
};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError as Error};

/// Types that can be converted to a vector of elements that implement the `Field Gadget` trait.
pub trait ToConstraintFieldGadget<ConstraintF: PrimeField> {
    type FieldGadget: FieldGadget<ConstraintF, ConstraintF>;

    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, Error>;
}

impl<ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF> for FpGadget<ConstraintF> {
    type FieldGadget = Self;

    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, Error> {
        Ok(vec![self.clone()])
    }
}

impl<ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF> for Vec<FpGadget<ConstraintF>> {
    type FieldGadget = FpGadget<ConstraintF>;

    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(&self, _cs: CS) -> Result<Vec<Self::FieldGadget>, Error> {
        Ok(self.clone())
    }
}

impl<ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF> for [FpGadget<ConstraintF>] {
    type FieldGadget = FpGadget<ConstraintF>;

    #[inline]
    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, Error> {
        Ok(self.to_vec())
    }
}

impl<ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF> for () {
    type FieldGadget = FpGadget<ConstraintF>;

    #[inline]
    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, Error> {
        Ok(Vec::new())
    }
}

impl<M, ConstraintF, FG> ToConstraintFieldGadget<ConstraintF>
    for SWPAffineGadget<M, ConstraintF, FG>
where
    M: SWModelParameters,
    ConstraintF: PrimeField,
    FG: FieldGadget<M::BaseField, ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
{
    type FieldGadget = FpGadget<ConstraintF>;

    #[inline]
    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, Error> {
        let mut x_fe = self.x.to_field_gadget_elements(cs.ns(|| "x"))?;
        let y_fe = self.y.to_field_gadget_elements(cs.ns(|| "y"))?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M, ConstraintF, FG> ToConstraintFieldGadget<ConstraintF>
    for SWJAffineGadget<M, ConstraintF, FG>
where
    M: SWModelParameters,
    ConstraintF: PrimeField,
    FG: FieldGadget<M::BaseField, ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
{
    type FieldGadget = FpGadget<ConstraintF>;

    #[inline]
    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, Error> {
        let mut x_fe = self.x.to_field_gadget_elements(cs.ns(|| "x"))?;
        let y_fe = self.y.to_field_gadget_elements(cs.ns(|| "y"))?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M, ConstraintF, FG> ToConstraintFieldGadget<ConstraintF> for TEAffineGadget<M, ConstraintF, FG>
where
    M: TEModelParameters,
    ConstraintF: PrimeField,
    FG: FieldGadget<M::BaseField, ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
{
    type FieldGadget = FpGadget<ConstraintF>;

    #[inline]
    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, Error> {
        let mut x_fe = self.x.to_field_gadget_elements(cs.ns(|| "x"))?;
        let y_fe = self.y.to_field_gadget_elements(cs.ns(|| "y"))?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF> for [UInt8] {
    type FieldGadget = FpGadget<ConstraintF>;

    #[inline]
    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, Error>
    {
        // Convert [UInt8] to the underlying [Boolean] in big-endian form
        let bytes_to_bool_gs = self.iter().flat_map(|byte| {
            byte.into_bits_le().iter().rev().cloned().collect::<Vec<Boolean>>()
        }).collect::<Vec<Boolean>>();

        // Enforce packing (safely) bits into native field element gadgets
        let mut native_fe_gadgets = Vec::new();
        for (i, bits) in bytes_to_bool_gs.chunks(ConstraintF::Params::CAPACITY as usize).enumerate() {
            let fe_g = FpGadget::<ConstraintF>::from_bits(
                cs.ns(|| format!("pack into native fe {}", i)),
                bits
            )?;
            native_fe_gadgets.push(fe_g);
        }

        Ok(native_fe_gadgets)
    }
}

#[cfg(all(test, feature = "tweedle"))]
mod test {
    use algebra::{fields::tweedle::Fr, ToConstraintField};
    use r1cs_core::{ConstraintSystem, SynthesisMode, ConstraintSystemDebugger};
    use rand::{Rng, thread_rng};
    use crate::alloc::AllocGadget;
    use super::*;
    
    #[test]
    fn uint8_native_test() {
        let rng = &mut thread_rng();

        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

        // Generate random bytes and allocate them on circuit
        let random_bytes = (0..100).map(|_| rng.gen()).collect::<Vec<u8>>();
        let random_bytes_g = random_bytes
            .iter()
            .enumerate()
            .map(|(i, byte)| 
                UInt8::alloc(
                    cs.ns(|| format!("Alloc byte {}", i)),
                    || Ok(byte)
                ).unwrap()
            ).collect::<Vec<_>>();


        // Convert to field elements and assert equality
        let fes: Vec<Fr> = random_bytes.to_field_elements().unwrap();
        random_bytes_g
            .to_field_gadget_elements(cs.ns(|| "bytes to fe gadgets"))
            .unwrap()
            .into_iter()
            .zip(fes.into_iter())
            .for_each(|(fe_g, fe)| assert_eq!(fe, fe_g.get_value().unwrap()));

        if let Some(unsatisfied_constraint) = cs.which_is_unsatisfied() {
            println!("{:?}", unsatisfied_constraint);
            panic!("Constraints expected to be satisfied");
        }
    }
}
