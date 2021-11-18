use crate::prelude::*;
use algebra::{BigInteger, Field, FpParameters, Group, PrimeField};
use r1cs_core::{ConstraintSystem, SynthesisError};

use std::{borrow::Borrow, fmt::Debug};

pub mod curves;

pub use self::curves::short_weierstrass::{bls12, bn, mnt};

#[cfg(feature = "nonnative")]
pub mod nonnative;

pub trait GroupGadget<G: Group, ConstraintF: Field>:
    Sized
    + ToBytesGadget<ConstraintF>
    + EqGadget<ConstraintF>
    + ToBitsGadget<ConstraintF>
    + CondSelectGadget<ConstraintF>
    + AllocGadget<G, ConstraintF>
    + ConstantGadget<G, ConstraintF>
    + Clone
    + Debug
{
    type Value: Debug;
    type Variable;

    fn get_value(&self) -> Option<Self::Value>;

    fn get_variable(&self) -> Self::Variable;

    fn zero<CS: ConstraintSystem<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError>;

    fn is_zero<CS: ConstraintSystem<ConstraintF>>(&self, cs: CS)
        -> Result<Boolean, SynthesisError>;

    fn add<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>;

    fn sub<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let neg_other = other.negate(cs.ns(|| "Negate other"))?;
        self.add(cs.ns(|| "Self - other"), &neg_other)
    }

    fn add_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        other: &G,
    ) -> Result<Self, SynthesisError>;

    fn sub_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &G,
    ) -> Result<Self, SynthesisError> {
        let neg_other = -(*other);
        self.add_constant(cs.ns(|| "Self - other"), &neg_other)
    }

    fn double_in_place<CS: ConstraintSystem<ConstraintF>>(
        &mut self,
        cs: CS,
    ) -> Result<(), SynthesisError>;

    fn negate<CS: ConstraintSystem<ConstraintF>>(&self, cs: CS) -> Result<Self, SynthesisError>;

    /// Variable base exponentiation.
    /// Inputs must be specified in *little-endian* form.
    /// If the addition law is incomplete for the identity element,
    /// `result` must not be the identity element.
    fn mul_bits<'a, CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        bits: impl Iterator<Item = &'a Boolean>,
    ) -> Result<Self, SynthesisError> {
        let mut power = self.clone();
        let mut acc = Self::zero(cs.ns(|| "alloc acc"))?;
        for (i, bit) in bits.enumerate() {
            let new_encoded = acc.add(&mut cs.ns(|| format!("Add {}-th power", i)), &power)?;
            acc = Self::conditionally_select(
                &mut cs.ns(|| format!("Select {}", i)),
                bit.borrow(),
                &new_encoded,
                &acc,
            )?;
            power.double_in_place(&mut cs.ns(|| format!("{}-th Doubling", i)))?;
        }
        Ok(acc)
    }

    fn precomputed_base_scalar_mul<'a, CS, I, B>(
        &mut self,
        mut cs: CS,
        scalar_bits_with_base_powers: I,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<ConstraintF>,
        I: Iterator<Item = (B, &'a G)>,
        B: Borrow<Boolean>,
        G: 'a,
    {
        for (i, (bit, base_power)) in scalar_bits_with_base_powers.enumerate() {
            let new_encoded = self.add_constant(
                &mut cs.ns(|| format!("Add {}-th base power", i)),
                &base_power,
            )?;
            *self = Self::conditionally_select(
                &mut cs.ns(|| format!("Conditional Select {}", i)),
                bit.borrow(),
                &new_encoded,
                &self,
            )?;
        }
        Ok(())
    }

    /// Fixed base exponentiation, slighlty different interface from
    /// `precomputed_base_scalar_mul`. Inputs must be specified in
    /// *little-endian* form. If the addition law is incomplete for
    /// the identity element, `result` must not be the identity element.
    fn mul_bits_fixed_base<CS: ConstraintSystem<ConstraintF>>(
        base: &G,
        mut cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        let base_g = Self::from_value(cs.ns(|| "hardcode base"), base);
        base_g.mul_bits(cs, bits.iter())
    }

    fn precomputed_base_3_bit_signed_digit_scalar_mul<'a, CS, I, J, B>(
        _: CS,
        _: &[B],
        _: &[J],
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<ConstraintF>,
        I: Borrow<[Boolean]>,
        J: Borrow<[I]>,
        B: Borrow<[G]>,
    {
        Err(SynthesisError::AssignmentMissing)
    }

    fn precomputed_base_multiscalar_mul<'a, CS, T, I, B>(
        mut cs: CS,
        bases: &[B],
        scalars: I,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<ConstraintF>,
        T: 'a + ToBitsGadget<ConstraintF> + ?Sized,
        I: Iterator<Item = &'a T>,
        B: Borrow<[G]>,
    {
        let mut result = Self::zero(&mut cs.ns(|| "Declare Result"))?;
        // Compute ∏(h_i^{m_i}) for all i.
        for (i, (bits, base_powers)) in scalars.zip(bases).enumerate() {
            let base_powers = base_powers.borrow();
            let bits = bits.to_bits(&mut cs.ns(|| format!("Convert Scalar {} to bits", i)))?;
            result.precomputed_base_scalar_mul(
                cs.ns(|| format!("Chunk {}", i)),
                bits.iter().zip(base_powers),
            )?;
        }
        Ok(result)
    }

    fn cost_of_add() -> usize;

    fn cost_of_double() -> usize;
}

pub trait EndoMulCurveGadget<G: Group, ConstraintF: Field>: GroupGadget<G, ConstraintF> {
    fn apply_endomorphism<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Self, SynthesisError>;

    fn endo_mul<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError>;
}

/// Pre-checks for vbSM with incomplete arithmetic using Hopwood algorithm (https://github.com/zcash/zcash/issues/3924) :
/// - 'self' must be non-trivial and in the prime order subgroup
/// - 'bits', in little endian, must be of length <= than the scalar field modulus.
///           and must not be equal to {0, p-2, p-1, p, p+1}.
#[inline]
pub(crate) fn check_mul_bits_inputs<G: Group>(
    base: &G,
    mut bits: Vec<bool>,
) -> Result<(), SynthesisError> {
    // bits must be smaller than the scalar field modulus
    if bits.len() > G::ScalarField::size_in_bits() {
        return Err(SynthesisError::Other(format!(
            "Input bits size: {}, max allowed size: {}",
            bits.len(),
            G::ScalarField::size_in_bits()
        )));
    }

    // Reverse bits
    bits.reverse();

    // self must not be trivial
    if base.is_zero() {
        return Err(SynthesisError::Other("Base point is trivial".to_owned()));
    }

    // self must be on curve and in the prime order subgroup
    if !base.is_valid() {
        return Err(SynthesisError::Other("Invalid base point".to_owned()));
    }

    // Read Bigint from bits
    let bits_val = <G::ScalarField as PrimeField>::BigInt::from_bits(bits.as_slice());

    // bits_val != 0
    if bits_val.is_zero() {
        return Err(SynthesisError::Other("Scalar must not be zero".to_owned()));
    }

    // bits_val != p
    let mut to_compare = <G::ScalarField as PrimeField>::Params::MODULUS;
    if bits_val == to_compare {
        return Err(SynthesisError::Other(
            "Scalar must not be equal to modulus".to_owned(),
        ));
    }

    // bits_val != p + 1
    assert!(!to_compare.add_nocarry(&<G::ScalarField as PrimeField>::BigInt::from(1)));
    if bits_val == to_compare {
        return Err(SynthesisError::Other(
            "Scalar must not be equal to modulus + 1".to_owned(),
        ));
    }

    // bits_val != p - 1
    assert!(!to_compare.sub_noborrow(&<G::ScalarField as PrimeField>::BigInt::from(2)));
    if bits_val == to_compare {
        return Err(SynthesisError::Other(
            "Scalar must not be equal to modulus - 1".to_owned(),
        ));
    }

    // bits_val != p - 2
    assert!(!to_compare.sub_noborrow(&<G::ScalarField as PrimeField>::BigInt::from(1)));
    if bits_val == to_compare {
        return Err(SynthesisError::Other(
            "Scalar must not be equal to modulus - 2".to_owned(),
        ));
    }

    Ok(())
}

/// Pre-checks for fbSM due to incomplete arithmetic as in our implementation.
/// [b_{n-1},...,b_0] are big endian scalar bits, padded with zeros to
/// the next multiple of two bits.
///     1. [b_n-1, ..., b_1, b_0] != 0 mod p
///     2. [b_n-1, ..., b_1, b_0] != 3*(2^n - 1) mod p
/// If n >= len(scalar field modulus), then we must check additionally
///     3. 2 * [b_n-1, ..., b_1, b_0] != 3*(2^n - 1) mod p
///     4. 2 *  [b_n-1, ..., b_1, b_0] != [b_n-1, b_n-2] * (2^n) - 3 mod p.
#[inline]
pub(crate) fn check_mul_bits_fixed_base_inputs<G: Group>(
    base: &G,
    bits: Vec<bool>,
) -> Result<(), SynthesisError> {
    use algebra::FromBits;

    // base must not be trivial
    if base.is_zero() {
        return Err(SynthesisError::Other("Base point is trivial".to_owned()));
    }

    // base must be on curve and in the prime order subgroup
    if !base.is_valid() {
        return Err(SynthesisError::Other("Invalid base point".to_owned()));
    }

    // Read FE from bits (read_bits() will remove leading zeros)
    let bits_val = G::ScalarField::read_bits(bits.clone())
        .map_err(|e| SynthesisError::Other(e.to_string()))?;

    let one = G::ScalarField::one();
    let two = one.double();
    let two_to_n = two.pow(&[bits.len() as u64]);
    let three = two + &one;
    let three_times_two_to_n_minus_one = three * &(two_to_n - &one);

    // [b_n-1, ..., b_1, b_0] != 0
    if bits_val == G::ScalarField::zero() {
        return Err(SynthesisError::Other(
            "[b_n-1, ..., b_1, b_0] != 0".to_owned(),
        ));
    }

    // [b_n-1, ..., b_1, b_0] != 3*(2^n - 1)
    if bits_val == three_times_two_to_n_minus_one {
        return Err(SynthesisError::Other(
            "[b_n-1, ..., b_1, b_0] != 3*(2^n - 1)".to_owned(),
        ));
    }

    if bits.len() >= G::ScalarField::size_in_bits() {
        // 2 *  [b_n-1, ..., b_1, b_0] != 3*(2^n - 1)
        if bits_val.double() == three_times_two_to_n_minus_one {
            return Err(SynthesisError::Other(
                "2 *  [b_n-1, ..., b_1, b_0] != 3*(2^n - 1)".to_owned(),
            ));
        }

        // 2 *  [b_n-1, ..., b_1, b_0] != [b_n-1, b_n-2] * (2^n) - 3
        let msb_val = G::ScalarField::read_bits((&bits[..2]).to_vec()).unwrap();
        let rhs = (msb_val * &two_to_n) - &three;
        if bits_val.double() == rhs {
            return Err(SynthesisError::Other(
                "2 *  [b_n-1, ..., b_1, b_0] != [b_n-1, b_n-2] * (2^n) - 3".to_owned(),
            ));
        }
    }

    Ok(())
}

/// The 'constant' length transformation for scalar multiplication in a group
/// with scalar field `ScalarF`.
/// Implements the non-native big integer addition of the scalar, given as
/// little endian vector of Boolean gadgets `bits`, and the modulus of the
/// scalar field. The result is a vector of Booleans in little-endian
/// always one bit longer than the scalar field modulus, possibly having
/// a leading zero.
/// This costs roughly ( n + 1 ) * num_limbs constraints
pub(crate) fn scalar_bits_to_constant_length<
    'a,
    ConstraintF: PrimeField,
    ScalarF: PrimeField,
    CS: ConstraintSystem<ConstraintF>,
>(
    mut cs: CS,
    bits: Vec<Boolean>,
) -> Result<Vec<Boolean>, SynthesisError> {
    use crate::fields::fp::FpGadget;

    if bits.len() > ScalarF::size_in_bits() {
        Err(SynthesisError::Other(format!(
            "Input bits size: {}, max allowed size: {}",
            bits.len(),
            ScalarF::size_in_bits()
        )))?
    }

    // bits per limb must not exceed the CAPACITY minus one bit, which is
    // reserved for the addition.
    let bits_per_limb = std::cmp::min(
        (ConstraintF::Params::CAPACITY - 1) as usize,
        ScalarF::size_in_bits(),
    );
    // ceil(ScalarF::size_in_bits()/bits_per_limb)
    // let num_limbs = (ScalarF::size_in_bits() + bits_per_limb - 1)/bits_per_limb;

    // Convert the scalar field modulus `MODULUS` to its vector of limbs,
    // little endian ordered.

    let scalar_char = &ScalarF::Params::MODULUS;
    let mut char_bits = scalar_char.to_bits();
    char_bits.reverse(); // little endian, including trailing zeros

    let char_limbs: Vec<ConstraintF> = char_bits[..ScalarF::size_in_bits()]
        .chunks(bits_per_limb)
        .map(|chunk| {
            // read_bits for PrimeField takes big endian order
            let mut chunk_rev = chunk.to_vec();
            chunk_rev.reverse();
            let limb = ConstraintF::read_bits(chunk_rev.to_vec());

            limb
        })
        .collect::<Result<_, _>>()?;

    // Pad `bits` to the same length as the scalar field characteristic,
    // and pack them into its limbs.
    let to_append = ScalarF::size_in_bits() - bits.len();
    let mut bits_padded = bits;
    bits_padded.append(&mut vec![Boolean::Constant(false); to_append]);

    let scalar_limbs = bits_padded
        .chunks(bits_per_limb)
        .enumerate()
        .map(|(i, chunk)| {
            // from_bits() assumes big endian vector of bits
            let mut chunk_rev = chunk.to_vec();
            chunk_rev.reverse();
            let limb = FpGadget::<ConstraintF>::from_bits(
                cs.ns(|| format!("packing scalar limb {}", i)),
                &chunk_rev.to_vec(),
            )?;

            Ok(limb)
        })
        .collect::<Result<Vec<FpGadget<ConstraintF>>, SynthesisError>>()?;

    // We compute the sum over the limbs taking carries into account
    let mut sum_limbs_bits: Vec<Boolean> = Vec::with_capacity(ScalarF::size_in_bits() + 1); // LE
    let mut carry_bit = Boolean::Constant(false);
    let mut to_be_processed = ScalarF::size_in_bits();
    let mut used_in_limb: usize;

    for (i, (scalar_limb, char_limb)) in scalar_limbs
        .into_iter()
        .zip(char_limbs.into_iter())
        .enumerate()
    {
        if to_be_processed < bits_per_limb {
            used_in_limb = to_be_processed;
        } else {
            used_in_limb = bits_per_limb;
        }

        // add the limb of the scalar with that of `MODULUS`
        let mut sum_limb = scalar_limb.add_constant(
            cs.ns(|| format!("scalar_limb + char_limb {}", i)),
            &char_limb,
        )?;

        // add the previous carry to the limb
        sum_limb = sum_limb.conditionally_add_constant(
            cs.ns(|| format!("add carry {}", i)),
            &carry_bit,
            ConstraintF::one(),
        )?;

        // unpack `sum_limb` into its `used_in_limb + 1` many bits.
        let to_skip =
            <ConstraintF::BasePrimeField as PrimeField>::size_in_bits() - (used_in_limb + 1);
        let mut sum_limb_bits = sum_limb.to_bits_with_length_restriction(
            cs.ns(|| format!("sum_limb to_bits_with_length_restriction {}", i)),
            to_skip,
        )?;
        sum_limb_bits.reverse();
        // The leading bit is the carry for the next significant limb
        carry_bit = sum_limb_bits.pop().unwrap();

        sum_limbs_bits.append(&mut sum_limb_bits);
        to_be_processed -= used_in_limb;
    }

    assert_eq!(to_be_processed, 0, "not all bits processed");

    // The last carry is part of the result.
    sum_limbs_bits.push(carry_bit);

    assert_eq!(sum_limbs_bits.len(), ScalarF::size_in_bits() + 1);
    Ok(sum_limbs_bits)
}

#[cfg(test)]
pub(crate) mod test {
    use algebra::{
        BigInteger, EndoMulCurve, Field, FpParameters, Group, PrimeField, ProjectiveCurve, ToBits,
        UniformRand,
    };
    use r1cs_core::ConstraintSystem;

    use crate::groups::EndoMulCurveGadget;
    use crate::{prelude::*, test_constraint_system::TestConstraintSystem};
    use rand::thread_rng;

    #[allow(dead_code)]
    pub(crate) fn group_test<
        ConstraintF: Field,
        G: Group,
        GG: GroupGadget<G, ConstraintF, Value = G>,
    >() {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        let a: G = UniformRand::rand(&mut thread_rng());
        let b: G = UniformRand::rand(&mut thread_rng());

        let a = GG::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
        let b = GG::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

        let zero = GG::zero(cs.ns(|| "Zero")).unwrap();

        // a + 0 = a
        assert_eq!(a.add(cs.ns(|| "a_plus_zero"), &zero).unwrap(), a);
        // a - 0 = a
        assert_eq!(a.sub(cs.ns(|| "a_minus_zero"), &zero).unwrap(), a);
        // a - a = 0
        assert_eq!(a.sub(cs.ns(|| "a_minus_a"), &a).unwrap(), zero);

        // a + b = b + a
        let a_b = a.add(cs.ns(|| "a_plus_b"), &b).unwrap();
        let b_a = b.add(cs.ns(|| "b_plus_a"), &a).unwrap();
        assert_eq!(a_b, b_a);
        // (a + b) + a = a + (b + a)
        let ab_a = a_b.add(&mut cs.ns(|| "a_b_plus_a"), &a).unwrap();
        let a_ba = a.add(&mut cs.ns(|| "a_plus_b_a"), &b_a).unwrap();
        assert_eq!(ab_a, a_ba);

        // a.double() = a + a
        let a_a = a.add(cs.ns(|| "a + a"), &a).unwrap();
        let mut a2 = a.clone();
        a2.double_in_place(cs.ns(|| "2a")).unwrap();
        assert_eq!(a2, a_a);
        // b.double() = b + b
        let mut b2 = b.clone();
        b2.double_in_place(cs.ns(|| "2b")).unwrap();
        let b_b = b.add(cs.ns(|| "b + b"), &b).unwrap();
        assert_eq!(b2, b_b);

        let _ = a.to_bytes(&mut cs.ns(|| "ToBytes")).unwrap();
        let _ = a.to_bytes_strict(&mut cs.ns(|| "ToBytes Strict")).unwrap();

        let _ = b.to_bytes(&mut cs.ns(|| "b ToBytes")).unwrap();
        let _ = b
            .to_bytes_strict(&mut cs.ns(|| "b ToBytes Strict"))
            .unwrap();
        assert!(cs.is_satisfied());

        scalar_bits_to_constant_length_test::<<ConstraintF as Field>::BasePrimeField, G>();
    }

    // To be called by curves with incomplete arithmetics. It is equal to the one above minus
    // checks that trigger exceptional cases due to incomplete arithmetic
    // (e.g a + a = a.double(), a + 0 = a, and so on).
    #[allow(dead_code)]
    pub(crate) fn group_test_with_incomplete_add<
        ConstraintF: Field,
        G: Group,
        GG: GroupGadget<G, ConstraintF, Value = G>,
    >() {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        let a_native: G = UniformRand::rand(&mut thread_rng());
        let b_native: G = UniformRand::rand(&mut thread_rng());

        let a = GG::alloc(&mut cs.ns(|| "generate_a"), || Ok(a_native)).unwrap();
        let b = GG::alloc(&mut cs.ns(|| "generate_b"), || Ok(b_native)).unwrap();

        let _zero = GG::zero(cs.ns(|| "Zero")).unwrap();

        // a + b = b + a
        let a_b = a.add(cs.ns(|| "a_plus_b"), &b).unwrap();
        let b_a = b.add(cs.ns(|| "b_plus_a"), &a).unwrap();
        assert_eq!(a_b, b_a);

        // (a + b) + a = a + (b + a)
        let ab_a = a_b.add(&mut cs.ns(|| "a_b_plus_a"), &a).unwrap();
        let a_ba = a.add(&mut cs.ns(|| "a_plus_b_a"), &b_a).unwrap();
        assert_eq!(ab_a, a_ba);

        // a.double() + b = (a + b) + a: Testing double() using b as shift
        let mut a2 = a.clone();
        a2.double_in_place(cs.ns(|| "2a")).unwrap();
        let a2_b = a2.add(cs.ns(|| "2a + b"), &b).unwrap();

        let a_b_a = a
            .add(cs.ns(|| "a + b"), &b)
            .unwrap()
            .add(cs.ns(|| "a + b + a"), &a)
            .unwrap();
        assert_eq!(a2_b, a_b_a);

        // (b.double() + a) = (b + a) + b: Testing double() using a as shift
        let mut b2 = b.clone();
        b2.double_in_place(cs.ns(|| "2b")).unwrap();
        let b2_a = b2.add(cs.ns(|| "2b + a"), &a).unwrap();

        let b_a_b = b
            .add(cs.ns(|| "b + a"), &a)
            .unwrap()
            .add(cs.ns(|| "b + a + b"), &b)
            .unwrap();
        assert_eq!(b2_a, b_a_b);

        let _ = a.to_bytes(&mut cs.ns(|| "ToBytes")).unwrap();
        let _ = a.to_bytes_strict(&mut cs.ns(|| "ToBytes Strict")).unwrap();

        let _ = b.to_bytes(&mut cs.ns(|| "b ToBytes")).unwrap();
        let _ = b
            .to_bytes_strict(&mut cs.ns(|| "b ToBytes Strict"))
            .unwrap();
        assert!(cs.is_satisfied());

        scalar_bits_to_constant_length_test::<<ConstraintF as Field>::BasePrimeField, G>();
    }

    /// Tests the 'constant' length transformation of `scalar_bits_to_constant_length` against
    /// the result of 'native' big integer arithmetics.
    #[allow(dead_code)]
    fn scalar_bits_to_constant_length_test<ConstraintF: PrimeField, G: Group>() {
        for _ in 0..30 {
            let mut cs = TestConstraintSystem::<ConstraintF>::new();
            let rng = &mut thread_rng();

            let a = G::ScalarField::rand(rng);
            let mut a_bigint = a.into_repr();
            println!("scalar bigint: {}", a_bigint);
            println!(
                "modulus bigint: {}",
                <G::ScalarField as PrimeField>::Params::MODULUS
            );
            // the 'native' addition of the scalar a and the scalar field modulus
            let carry = a_bigint.add_nocarry(&<G::ScalarField as PrimeField>::Params::MODULUS);
            println!("sum bigint: {}", a_bigint);
            // add_nocarry should never return a non-zero as the BigInt's are always oversized to
            // prevent this.
            assert_eq!(carry, false, "add_nocarry overflow.");

            // get the bits in little endian order.
            // Note: `to_bits()` seems not to skip leading zeroes
            let mut native_result = a_bigint.to_bits();
            native_result.reverse();

            // Checking plausability of native sum
            let expected_len = <G::ScalarField as PrimeField>::size_in_bits() + 1;
            assert_eq!(
                native_result[expected_len..],
                vec![false; native_result.len() - expected_len],
                "unexpected large native result"
            );
            assert!(
                native_result[expected_len - 1]
                    || (!native_result[expected_len - 1] && native_result[expected_len - 2]),
                "unexpected value of native result"
            );

            // Alloc a vector of Boolean Gadgets with values according to the scalar bits, little endian.
            let mut a_bits_gadget =
                Vec::<Boolean>::alloc(cs.ns(|| "a bits"), || Ok(a.write_bits())).unwrap();
            a_bits_gadget.reverse();

            // Compute the sum by means of the arithmetic circuit of `scalar_bits_to_constant_length()`
            let gadget_result =
                crate::groups::scalar_bits_to_constant_length::<_, G::ScalarField, _>(
                    cs.ns(|| "a bits to constant length"),
                    a_bits_gadget,
                )
                .unwrap()
                .into_iter()
                .map(|b| b.get_value().unwrap())
                .collect::<Vec<bool>>();

            // check equality with the native sum
            assert_eq!(
                expected_len,
                gadget_result.len(),
                "Native and circuit length not equal"
            );
            assert_eq!(
                native_result[..expected_len],
                gadget_result,
                "Native and circuit value not equal"
            );

            assert!(cs.is_satisfied());
        }
    }

    #[allow(dead_code)]
    pub(crate) fn mul_bits_native_test<
        ConstraintF: Field,
        G: Group,
        GG: GroupGadget<G, ConstraintF, Value = G>,
    >() {
        let mut cs: TestConstraintSystem<ConstraintF> = TestConstraintSystem::<ConstraintF>::new();
        let rng = &mut thread_rng();

        // Sample random base
        let g: G = UniformRand::rand(rng);
        let gg = GG::alloc(cs.ns(|| "generate_g"), || Ok(g)).unwrap();

        // Sample random scalar
        let a = G::ScalarField::rand(rng);

        // Alloc its bits on the circuit
        let mut a_bits = Vec::<Boolean>::alloc(cs.ns(|| "a bits"), || Ok(a.write_bits())).unwrap();
        a_bits.reverse();

        // Variable base scalar multiplication
        let x = cs.num_constraints();
        let a_times_gg_vb = gg.mul_bits(cs.ns(|| "a * G"), a_bits.iter()).unwrap();
        println!(
            "Variable base SM exponent len {}, num_constraints: {}",
            a_bits.len(),
            cs.num_constraints() - x
        );

        // Fixed base scalar multiplication
        let x = cs.num_constraints();
        let a_times_gg_fb =
            GG::mul_bits_fixed_base(&g, cs.ns(|| "fb a * G"), a_bits.as_slice()).unwrap();
        println!(
            "Fixed base SM exponent len {}, num_constraints: {}",
            a_bits.len(),
            cs.num_constraints() - x
        );

        // Compare with native results
        assert_eq!(a_times_gg_vb.get_value().unwrap(), g.mul(&a));
        assert_eq!(a_times_gg_fb.get_value().unwrap(), g.mul(&a));

        assert!(cs.is_satisfied());
    }

    #[allow(dead_code)]
    pub(crate) fn mul_bits_additivity_test<
        ConstraintF: Field,
        G: Group,
        GG: GroupGadget<G, ConstraintF, Value = G>,
    >() {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();
        let rng = &mut thread_rng();

        let g: G = UniformRand::rand(rng);
        let gg = GG::alloc(cs.ns(|| "generate_g"), || Ok(g)).unwrap();

        let a = G::ScalarField::rand(rng);
        let b = G::ScalarField::rand(rng);
        //let ab = a * &b;
        let a_plus_b = a + &b;

        let mut a_bits = Vec::<Boolean>::alloc(cs.ns(|| "a bits"), || Ok(a.write_bits())).unwrap();
        a_bits.reverse();

        let mut b_bits = Vec::<Boolean>::alloc(cs.ns(|| "b bits"), || Ok(b.write_bits())).unwrap();
        b_bits.reverse();

        //let ab_bits = Vec::<Boolean>::alloc(cs.ns(|| "ab bits"), ||Ok(ab.write_bits())).unwrap();
        let mut a_plus_b_bits =
            Vec::<Boolean>::alloc(cs.ns(|| "a_plus_b bits"), || Ok(a_plus_b.write_bits())).unwrap();
        a_plus_b_bits.reverse();

        // Additivity test: a * G + b * G = (a + b) * G
        let a_times_gg_vb = gg.mul_bits(cs.ns(|| "a * G"), a_bits.iter()).unwrap();
        let a_times_gg_fb =
            GG::mul_bits_fixed_base(&g, cs.ns(|| "fb a * G"), a_bits.as_slice()).unwrap();

        let b_times_gg_vb = gg.mul_bits(cs.ns(|| "b * G"), b_bits.iter()).unwrap();
        let b_times_gg_fb =
            GG::mul_bits_fixed_base(&g, cs.ns(|| "fb b * G"), b_bits.as_slice()).unwrap();

        let a_plus_b_times_gg_vb = gg
            .mul_bits(cs.ns(|| "(a + b) * G"), a_plus_b_bits.iter())
            .unwrap();
        let a_plus_b_times_gg_fb =
            GG::mul_bits_fixed_base(&g, cs.ns(|| "fb (a + b) * G"), a_plus_b_bits.as_slice())
                .unwrap();

        a_times_gg_vb
            .add(cs.ns(|| "a * G + b * G"), &b_times_gg_vb)
            .unwrap()
            .enforce_equal(
                cs.ns(|| "a * G + b * G = (a + b) * G"),
                &a_plus_b_times_gg_vb,
            )
            .unwrap();

        a_times_gg_fb
            .add(cs.ns(|| "fb a * G + b * G"), &b_times_gg_fb)
            .unwrap()
            .enforce_equal(
                cs.ns(|| "fb a * G + b * G = (a + b) * G"),
                &a_plus_b_times_gg_fb,
            )
            .unwrap();
        assert!(cs.is_satisfied());
    }

    #[allow(dead_code)]
    pub(crate) fn mul_bits_test<
        ConstraintF: Field,
        G: Group,
        GG: GroupGadget<G, ConstraintF, Value = G>,
    >() {
        for _ in 0..10 {
            mul_bits_native_test::<ConstraintF, G, GG>();
            mul_bits_additivity_test::<ConstraintF, G, GG>();
        }
    }

    #[allow(dead_code)]
    pub(crate) fn endo_mul_test<
        ConstraintF: Field,
        G: ProjectiveCurve,
        GG: EndoMulCurveGadget<G, ConstraintF, Value = G>,
    >()
    where
        <G as ProjectiveCurve>::Affine: EndoMulCurve,
    {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        let a_native_proj = G::rand(&mut thread_rng());
        let a_native = a_native_proj.into_affine();
        let a = GG::alloc(&mut cs.ns(|| "generate_a"), || Ok(a_native_proj)).unwrap();

        let scalar: G::ScalarField = u128::rand(&mut thread_rng()).into();

        let b_native = scalar.into_repr().to_bits().as_slice()[0..128].to_vec();
        let b = b_native
            .iter()
            .map(|&bit| Boolean::constant(bit))
            .collect::<Vec<_>>();

        let r_native = a_native.endo_mul(b_native).unwrap();
        let r = a
            .endo_mul(cs.ns(|| "endo mul"), &b)
            .unwrap()
            .get_value()
            .unwrap();

        assert_eq!(r_native, r);
    }
}
