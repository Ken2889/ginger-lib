//! A module for representing 32 bit unsigned integers over a prime constraint field.
//! Besides elementary gadgets (such as toBits, toBytes, etc.) implements the bitwise
//! operations
//!     - rotl, rotr, shr, xor,
//! as well as
//!     - add_many, which performs the addition modulo 2^32 of a slice of operands,
//!     the result of which does exceed in length the capacity bound of the constraint
//!     field.
use algebra::{Field, FpParameters, PrimeField};

use r1cs_core::{ConstraintSystemAbstract, LinearCombination, SynthesisError};

use crate::{
    boolean::{AllocatedBit, Boolean},
    eq::MultiEq,
    prelude::*,
    Assignment,
};

/// Represents an interpretation of 32 `Boolean` objects as an
/// unsigned integer.
#[derive(Clone, Debug)]
pub struct UInt32 {
    // Least significant bit_gadget first
    pub bits: Vec<Boolean>,
    pub value: Option<u32>,
}

impl UInt32 {
    /// Construct a constant `UInt32` from a `u32`
    pub fn constant(value: u32) -> Self {
        let mut bits = Vec::with_capacity(32);

        let mut tmp = value;
        for _ in 0..32 {
            if tmp & 1 == 1 {
                bits.push(Boolean::constant(true))
            } else {
                bits.push(Boolean::constant(false))
            }

            tmp >>= 1;
        }

        UInt32 {
            bits,
            value: Some(value),
        }
    }

    /// Allocate a `UInt32` in the constraint system
    pub fn alloc<ConstraintF, CS>(mut cs: CS, value: Option<u32>) -> Result<Self, SynthesisError>
    where
        ConstraintF: Field,
        CS: ConstraintSystemAbstract<ConstraintF>,
    {
        let values = match value {
            Some(mut val) => {
                let mut v = Vec::with_capacity(32);

                for _ in 0..32 {
                    v.push(Some(val & 1 == 1));
                    val >>= 1;
                }

                v
            }
            None => vec![None; 32],
        };

        let bits = values
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.ns(|| format!("allocated bit_gadget {}", i)),
                    || v.get(),
                )?))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(UInt32 { bits, value })
    }

    /// Turns this `UInt32` into its little-endian byte order representation.
    pub fn to_bits_le(&self) -> Vec<Boolean> {
        self.bits.clone()
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `UInt32`.
    pub fn from_bits_le(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 32);

        let bits = bits.to_vec();

        let mut value = Some(0u32);
        for b in bits.iter().rev() {
            value.as_mut().map(|v| *v <<= 1);

            match b {
                &Boolean::Constant(b) => {
                    if b {
                        value.as_mut().map(|v| *v |= 1);
                    }
                }
                &Boolean::Is(ref b) => match b.get_value() {
                    Some(true) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(false) => {}
                    None => value = None,
                },
                &Boolean::Not(ref b) => match b.get_value() {
                    Some(false) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(true) => {}
                    None => value = None,
                },
            }
        }

        Self { bits, value }
    }

    pub fn into_bits_be(self) -> Vec<Boolean> {
        let mut ret = self.bits;
        ret.reverse();
        ret
    }

    pub fn from_bits_be(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 32);

        let mut value = Some(0u32);
        for b in bits {
            value.as_mut().map(|v| *v <<= 1);

            match b.get_value() {
                Some(true) => {
                    value.as_mut().map(|v| *v |= 1);
                }
                Some(false) => {}
                None => {
                    value = None;
                }
            }
        }

        UInt32 {
            value,
            bits: bits.iter().rev().cloned().collect(),
        }
    }

    pub fn rotl(&self, by: usize) -> Self {
        let by = by % 32;

        let new_bits = self
            .bits
            .iter()
            .skip(32 - by)
            .chain(self.bits.iter())
            .take(32)
            .cloned()
            .collect();

        UInt32 {
            bits: new_bits,
            value: self.value.map(|v| v.rotate_left(by as u32)),
        }
    }

    pub fn rotr(&self, by: usize) -> Self {
        let by = by % 32;

        let new_bits = self
            .bits
            .iter()
            .skip(by)
            .chain(self.bits.iter())
            .take(32)
            .cloned()
            .collect();

        UInt32 {
            bits: new_bits,
            value: self.value.map(|v| v.rotate_right(by as u32)),
        }
    }

    pub fn shr(&self, by: usize) -> Self {
        let by = by % 32;

        let fill = Boolean::constant(false);

        let new_bits = self
            .bits
            .iter() // The bits are least significant first
            .skip(by) // Skip the bits that will be lost during the shift
            .chain(Some(&fill).into_iter().cycle()) // Rest will be zeros
            .take(32) // Only 32 bits needed!
            .cloned()
            .collect();

        UInt32 {
            bits: new_bits,
            value: self.value.map(|v| v >> by as u32),
        }
    }

    /// XOR this `UInt32` with another `UInt32`
    pub fn xor<ConstraintF, CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        ConstraintF: Field,
        CS: ConstraintSystemAbstract<ConstraintF>,
    {
        let new_value = match (self.value, other.value) {
            (Some(a), Some(b)) => Some(a ^ b),
            _ => None,
        };

        let bits = self
            .bits
            .iter()
            .zip(other.bits.iter())
            .enumerate()
            .map(|(i, (a, b))| Boolean::xor(cs.ns(|| format!("xor of bit_gadget {}", i)), a, b))
            .collect::<Result<_, _>>()?;

        Ok(UInt32 {
            bits,
            value: new_value,
        })
    }

    /// Perform addition modulo 2^32 of several `UInt32` objects.
    pub fn addmany<ConstraintF, CS, M>(mut cs: M, operands: &[Self]) -> Result<Self, SynthesisError>
    where
        ConstraintF: PrimeField,
        CS: ConstraintSystemAbstract<ConstraintF>,
        M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>,
    {
        // Make some arbitrary bounds for ourselves to avoid overflows
        // in the scalar field

        assert!(ConstraintF::Params::MODULUS_BITS >= 64);
        assert!(operands.len() >= 2); // Weird trivial cases that should never happen
                                      // TODO: Check this bound. Is it really needed ?
        assert!(operands.len() <= 10);

        // Compute the maximum value of the sum so we allocate enough bits for
        // the result
        let mut max_value = (operands.len() as u64) * (u64::from(u32::max_value()));

        // Keep track of the resulting value
        let mut result_value = Some(0u64);

        // This is a linear combination that we will enforce to equal the
        // output
        let mut lc = LinearCombination::zero();

        let mut all_constants = true;

        // Iterate over the operands
        for op in operands {
            // Accumulate the value
            match op.value {
                Some(val) => {
                    result_value.as_mut().map(|v| *v += u64::from(val));
                }
                None => {
                    // If any of our operands have unknown value, we won't
                    // know the value of the result
                    result_value = None;
                }
            }

            // Cumulate the terms that correspond to the bits in op to the
            // overall LC
            let mut coeff = ConstraintF::one();
            for bit in &op.bits {
                // adds 2^i * bit[i] to the lc
                lc = lc + &bit.lc(CS::one(), coeff);

                // all_constants = all_constants & bit.is_constant()
                all_constants &= bit.is_constant();

                coeff = coeff.double();
            }
        }

        // The value of the actual result is modulo 2^32
        let modular_value = result_value.map(|v| v as u32);

        // In case that all operants are constant UInt32 it is enough to return a constant.
        if all_constants && modular_value.is_some() {
            // We can just return a constant, rather than
            // unpacking the result into allocated bits.

            return Ok(UInt32::constant(modular_value.unwrap()));
        }

        // Storage area for the resulting bits
        let mut result_bits = vec![];

        // Linear combination representing the output,
        // for comparison with the sum of the operands
        let mut result_lc = LinearCombination::zero();

        // Allocate each bit of the result from result_val
        let mut coeff = ConstraintF::one();
        let mut i = 0;
        while max_value != 0 {
            // Allocate the bit using result_value
            let b = AllocatedBit::alloc(cs.ns(|| format!("result bit {}", i)), || {
                result_value.map(|v| (v >> i) & 1 == 1).get()
            })?;

            // Add this bit to the result combination
            result_lc += (coeff, b.get_variable());

            result_bits.push(b.into());

            max_value >>= 1;
            i += 1;
            coeff = coeff.double();
        }

        // Enforce equality between the sum and result by aggregating it
        // in the MultiEq
        cs.get_root().enforce_equal(i, &lc, &result_lc);

        // Discard carry bits that we don't care about
        result_bits.truncate(32);

        Ok(UInt32 {
            bits: result_bits,
            value: modular_value,
        })
    }
}

impl<ConstraintF: Field> ToBytesGadget<ConstraintF> for UInt32 {
    #[inline]
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let value_chunks = match self.value.map(|val| {
            use algebra::bytes::ToBytes;
            let mut bytes = [0u8; 4];
            val.write(bytes.as_mut()).unwrap();
            bytes
        }) {
            Some(chunks) => [
                Some(chunks[0]),
                Some(chunks[1]),
                Some(chunks[2]),
                Some(chunks[3]),
            ],
            None => [None, None, None, None],
        };
        let mut bytes = Vec::new();
        for (i, chunk8) in self.to_bits_le().chunks(8).into_iter().enumerate() {
            let byte = UInt8 {
                bits: chunk8.to_vec(),
                value: value_chunks[i],
            };
            bytes.push(byte);
        }

        Ok(bytes)
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl PartialEq for UInt32 {
    fn eq(&self, other: &Self) -> bool {
        self.value.is_some() && other.value.is_some() && self.value == other.value
    }
}

impl Eq for UInt32 {}

impl<ConstraintF: Field> EqGadget<ConstraintF> for UInt32 {
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        self.bits.as_slice().is_eq(cs, &other.bits)
    }

    fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.bits
            .conditional_enforce_equal(cs, &other.bits, should_enforce)
    }

    fn conditional_enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.bits
            .conditional_enforce_not_equal(cs, &other.bits, should_enforce)
    }
}

#[cfg(all(test, feature = "bls12_381"))]
mod test {
    use super::UInt32;
    use crate::{bits::boolean::Boolean, eq::MultiEq};
    use algebra::fields::{bls12_381::Fr, Field};
    use r1cs_core::{
        ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
    };
    use rand::{Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_uint32_from_bits() {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        for _ in 0..1000 {
            let v = (0..32)
                .map(|_| Boolean::constant(rng.gen()))
                .collect::<Vec<_>>();

            let b = UInt32::from_bits_le(&v);

            for (i, bit_gadget) in b.bits.iter().enumerate() {
                match bit_gadget {
                    &Boolean::Constant(bit_gadget) => {
                        assert!(bit_gadget == ((b.value.unwrap() >> i) & 1 == 1));
                    }
                    _ => unreachable!(),
                }
            }

            let expected_to_be_same = b.to_bits_le();

            for x in v.iter().zip(expected_to_be_same.iter()) {
                match x {
                    (&Boolean::Constant(true), &Boolean::Constant(true)) => {}
                    (&Boolean::Constant(false), &Boolean::Constant(false)) => {}
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_uint32_xor() {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        for _ in 0..1000 {
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

            let a: u32 = rng.gen();
            let b: u32 = rng.gen();
            let c: u32 = rng.gen();

            let mut expected = a ^ b ^ c;

            let a_bit = UInt32::alloc(cs.ns(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt32::constant(b);
            let c_bit = UInt32::alloc(cs.ns(|| "c_bit"), Some(c)).unwrap();

            let r = a_bit.xor(cs.ns(|| "first xor"), &b_bit).unwrap();
            let r = r.xor(cs.ns(|| "second xor"), &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    &Boolean::Not(ref b) => {
                        assert!(b.get_value().unwrap() != (expected & 1 == 1));
                    }
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    fn test_uint32_addmany_constants() {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        for _ in 0..1000 {
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

            let num_operands = 10;

            let operands_val = (0..num_operands).map(|_| rng.gen()).collect::<Vec<u32>>();
            let mut expected = operands_val.iter().fold(0u32, |acc, x| x.wrapping_add(acc));

            let operands_gadget = operands_val
                .into_iter()
                .map(UInt32::constant)
                .collect::<Vec<UInt32>>();

            let r = {
                let mut cs = MultiEq::new(&mut cs);
                let r = UInt32::addmany(cs.ns(|| "addition"), operands_gadget.as_slice()).unwrap();
                r
            };
            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(_) => panic!(),
                    &Boolean::Not(_) => panic!(),
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }

            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_uint32_addmany() {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        for _ in 0..1000 {
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

            let num_operands = 10;

            let operands_val = (0..num_operands).map(|_| rng.gen()).collect::<Vec<u32>>();
            let mut expected = operands_val.iter().fold(0u32, |acc, x| x.wrapping_add(acc));

            let operands_gadget = operands_val
                .into_iter()
                .enumerate()
                .map(|(i, val)| {
                    UInt32::alloc(cs.ns(|| format!("alloc u32 {}", i)), Some(val)).unwrap()
                })
                .collect::<Vec<UInt32>>();

            let r = {
                let mut cs = MultiEq::new(&mut cs);
                let r = UInt32::addmany(cs.ns(|| "addition"), operands_gadget.as_slice()).unwrap();
                r
            };

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    &Boolean::Not(ref b) => {
                        assert!(b.get_value().unwrap() != (expected & 1 == 1));
                    }
                    &Boolean::Constant(_) => unreachable!(),
                }

                expected >>= 1;
            }

            // Flip a bit_gadget and see if the addition constraint still works
            if cs.get("addition/result bit 0/boolean").is_zero() {
                cs.set("addition/result bit 0/boolean", Field::one());
            } else {
                cs.set("addition/result bit 0/boolean", Field::zero());
            }

            assert!(!cs.is_satisfied());
        }
    }

    #[test]
    fn test_uint32_rotr() {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let mut num = rng.gen();

        let a = UInt32::constant(num);

        for i in 0..32 {
            let b = a.rotr(i);

            assert!(b.value.unwrap() == num);

            let mut tmp = num;
            for b in &b.bits {
                match b {
                    &Boolean::Constant(b) => {
                        assert_eq!(b, tmp & 1 == 1);
                    }
                    _ => unreachable!(),
                }

                tmp >>= 1;
            }

            num = num.rotate_right(1);
        }
    }

    #[test]
    fn test_uint32_rotl() {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let mut num = rng.gen();

        let a = UInt32::constant(num);

        for i in 0..32 {
            let b = a.rotl(i);

            assert!(b.value.unwrap() == num);

            let mut tmp = num;
            for b in &b.bits {
                match b {
                    &Boolean::Constant(b) => {
                        assert_eq!(b, tmp & 1 == 1);
                    }
                    _ => unreachable!(),
                }

                tmp >>= 1;
            }

            num = num.rotate_left(1);
        }
    }
}
