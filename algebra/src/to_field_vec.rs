use crate::{
    fields::{
        Field, FpParameters, PrimeField,
    },
    curves::{
        Curve,
        models::{SWModelParameters, TEModelParameters},
        short_weierstrass_jacobian::Jacobian,
        short_weierstrass_projective::Projective,
        twisted_edwards_extended::TEExtended,
    }, ToBits,
};

type Error = Box<dyn std::error::Error>;

macro_rules! slice_to_constraint_field {
    ($base: ident) => {
        impl<'a, F: Field> ToConstraintField<F> for &'a [$base] {
            fn to_field_elements(&self) -> Result<Vec<F>, Error> {
                ToConstraintField::<F>::to_field_elements(*self)
            }
        }
    };
}

/// Types that can be converted to a vector of `F` elements. Useful for specifying
/// how public inputs to a constraint system should be represented inside
/// that constraint system.
pub trait ToConstraintField<F: Field> {
    fn to_field_elements(&self) -> Result<Vec<F>, Error>;
}

impl<F: Field, T: ToConstraintField<F> + Clone, const N: usize> ToConstraintField<F> for [T; N] {
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        self.to_vec().to_field_elements()
    }
}

impl<F: Field, T: ToConstraintField<F>> ToConstraintField<F> for Vec<T> {
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        let mut fes = Vec::with_capacity(self.len());
        for elem in self.iter() {
            fes.append(&mut elem.to_field_elements()?);
        }
        Ok(fes)
    }
}

impl<F: Field> ToConstraintField<F> for F {
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        Ok(vec![*self])
    }
}

impl<ConstraintF: Field> ToConstraintField<ConstraintF> for () {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        Ok(Vec::new())
    }
}

impl<M: SWModelParameters, ConstraintF: Field> ToConstraintField<ConstraintF> for Jacobian<M>
    where
        M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        let affine = self.into_affine()?;
        let mut x_fe = affine.x.to_field_elements()?;
        let y_fe = affine.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M: SWModelParameters, ConstraintF: Field> ToConstraintField<ConstraintF> for Projective<M>
    where
        M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        let affine = self.into_affine()?; // Affine coordinates are defined even if `self` is the neutral elements
        let mut x_fe = affine.x.to_field_elements()?;
        let y_fe = affine.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M: TEModelParameters, ConstraintF: Field> ToConstraintField<ConstraintF> for TEExtended<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        let affine = self.into_affine()?;
        let mut x_fe = affine.x.to_field_elements()?;
        let y_fe = affine.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<ConstraintF: Field> ToConstraintField<ConstraintF> for [u8] {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        self
            .write_bits()
            .to_field_elements()
    }
}

slice_to_constraint_field!(u8);

impl<'a, ConstraintF: Field> ToConstraintField<ConstraintF> for &'a str {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        self.as_bytes().to_field_elements()
    }
}

impl<ConstraintF: Field> ToConstraintField<ConstraintF> for [bool] {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        let max_size = <ConstraintF::BasePrimeField as PrimeField>::Params::CAPACITY as usize;
        let fes = self
            .chunks(max_size)
            .map(|chunk| ConstraintF::read_bits(chunk.to_vec()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(fes)
    }
}

slice_to_constraint_field!(bool);