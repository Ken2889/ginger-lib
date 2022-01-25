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
    },
};

type Error = Box<dyn std::error::Error>;

/// Types that can be converted to a vector of `F` elements. Useful for specifying
/// how public inputs to a constraint system should be represented inside
/// that constraint system.
pub trait ToConstraintField<F: Field> {
    fn to_field_elements(&self) -> Result<Vec<F>, Error>;
}

impl<'a, F: PrimeField, T: ToConstraintField<F>> ToConstraintField<F> for &'a [T] {
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        let mut fes = Vec::with_capacity(self.len());
        for elem in self.iter() {
            fes.append(&mut elem.to_field_elements()?);
        }
        Ok(fes)
    }
}

impl<F: PrimeField, T: ToConstraintField<F>> ToConstraintField<F> for Vec<T> {
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        self.as_slice().to_field_elements()
    }
}

impl<F: PrimeField> ToConstraintField<F> for F {
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        Ok(vec![*self])
    }
}

// Impl for base field
impl<F: Field> ToConstraintField<F> for [F] {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, Error> {
        Ok(self.to_vec())
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

impl<ConstraintF: PrimeField> ToConstraintField<ConstraintF> for [u8] {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        let max_size = <ConstraintF as PrimeField>::Params::CAPACITY / 8;
        let max_size = max_size as usize;
        let bigint_size = (<ConstraintF as PrimeField>::Params::MODULUS_BITS
            + <ConstraintF as PrimeField>::Params::REPR_SHAVE_BITS)
            / 8;
        let fes = self
            .chunks(max_size)
            .map(|chunk| {
                let mut chunk = chunk.to_vec();
                let len = chunk.len();
                for _ in len..(bigint_size as usize) {
                    chunk.push(0u8);
                }
                ConstraintF::read(chunk.as_slice())
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(fes)
    }
}

impl<ConstraintF: PrimeField> ToConstraintField<ConstraintF> for [bool] {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        let max_size = <ConstraintF as PrimeField>::Params::CAPACITY as usize;
        let fes = self
            .chunks(max_size)
            .map(|chunk| ConstraintF::read_bits(chunk.to_vec()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(fes)
    }
}

impl<ConstraintF: PrimeField> ToConstraintField<ConstraintF> for [u8; 32] {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        self.as_ref().to_field_elements()
    }
}
