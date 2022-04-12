use crate::darlin::accumulators::Error;
use algebra::Field;

pub trait ToDualField<F: Field> {
    fn to_dual_field_elements(&self) -> Result<Vec<F>, Error>;
}

impl<F: Field, T: ToDualField<F> + Clone, const N: usize> ToDualField<F> for [T; N] {
    fn to_dual_field_elements(&self) -> Result<Vec<F>, Error> {
        let mut fes = Vec::with_capacity(self.len());
        for elem in self.iter() {
            fes.append(&mut elem.to_dual_field_elements()?);
        }
        Ok(fes)
    }
}

impl<F: Field, T: ToDualField<F>> ToDualField<F> for Vec<T> {
    fn to_dual_field_elements(&self) -> Result<Vec<F>, Error> {
        let mut fes = Vec::with_capacity(self.len());
        for elem in self.iter() {
            fes.append(&mut elem.to_dual_field_elements()?);
        }
        Ok(fes)
    }
}

impl<F: Field> ToDualField<F> for () {
    #[inline]
    fn to_dual_field_elements(&self) -> Result<Vec<F>, Error> {
        Ok(Vec::new())
    }
}
