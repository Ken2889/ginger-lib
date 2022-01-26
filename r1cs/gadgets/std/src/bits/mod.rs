use crate::bits::{boolean::Boolean, uint8::UInt8};
use algebra::Field;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};

pub mod boolean;
pub mod uint32;
pub mod uint64;
pub mod uint8;

pub trait ToBitsGadget<ConstraintF: Field> {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError>;
}

pub trait FromBitsGadget<ConstraintF: Field>
where
    Self: Sized,
{
    /// Given a bit representation `bits` of bit len not bigger than CAPACITY
    /// (i.e. MODULUS - 1) of `Self` in *big endian* form, reconstructs a `Self`.
    fn from_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError>;
}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for Boolean {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }
}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for [Boolean] {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }
}
impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for Vec<Boolean> {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }
}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for [UInt8] {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut result = Vec::with_capacity(&self.len() * 8);
        for byte in self {
            result.extend_from_slice(&byte.into_bits_le());
        }
        Ok(result)
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits(cs)
    }
}

pub trait ToBytesGadget<ConstraintF: Field> {
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError>;
}

pub trait ToCompressedBitsGadget<ConstraintF: Field> {
    /// Enforce compression of an element through serialization of the x coordinate and storing
    /// a sign bit for the y coordinate. For GT elements we assume x <-> c1 and y <-> c0 to avoid
    /// confusion. When enforcing byte serialization of a field element, "x_in_field" and "y_in_field"
    /// flags could be set in order to enforce too that their bit representation is under the
    /// field modulus (default behaviour is both set to false).
    fn to_compressed<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError>;
}

impl<ConstraintF: Field> ToBytesGadget<ConstraintF> for UInt8 {
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        Ok(vec![self.clone()])
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        Ok(vec![self.clone()])
    }
}

impl<'a, ConstraintF: Field, T: 'a + ToBytesGadget<ConstraintF>> ToBytesGadget<ConstraintF>
    for &'a T
{
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        (*self).to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<'a, ConstraintF: Field, T: 'a + ToBytesGadget<ConstraintF>> ToBytesGadget<ConstraintF>
    for &'a [T]
{
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bytes = Vec::new();
        for (i, elem) in self.iter().enumerate() {
            bytes.append(&mut elem.to_bytes(cs.ns(|| format!("elem {} to bytes", i)))?);
        }
        Ok(bytes)
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bytes = Vec::new();
        for (i, elem) in self.iter().enumerate() {
            bytes.append(&mut elem.to_bytes_strict(cs.ns(|| format!("elem {} to bytes strict", i)))?);
        }
        Ok(bytes)
    }
}

impl<ConstraintF: Field> ToBytesGadget<ConstraintF> for [UInt8] {
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        (&self).to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        (&self).to_bytes_strict(cs)
    }
}

impl<ConstraintF: Field, T: ToBytesGadget<ConstraintF>> ToBytesGadget<ConstraintF>
    for Vec<T>
{
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.as_slice().to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.as_slice().to_bytes_strict(cs)
    }
}
