pub mod params;
pub use params::*;

use crate::{BigInteger, PrimeField};
use num_bigint::BigUint;
use num_traits::{Zero, One};

/// Obtain the value of limbs
pub fn limbs_to_value<SimulationF: PrimeField, ConstraintF: PrimeField>(limbs: Vec<ConstraintF>) -> SimulationF {
    let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

    let mut base_repr: <SimulationF as PrimeField>::BigInt = SimulationF::one().into_repr();

    // Convert 2^{(params.bits_per_limb - 1)} into the SimulationF then double the base
    // This is because 2^{(params.bits_per_limb)} might indeed be larger than the target field's prime.
    base_repr.muln((params.bits_per_limb - 1) as u32);
    let mut base = SimulationF::from_repr(base_repr);
    base = base + &base;

    let mut result = SimulationF::zero();
    let mut power = SimulationF::one();

    for limb in limbs.iter().rev() {
        let mut val = SimulationF::zero();
        let mut cur = SimulationF::one();

        for bit in limb.into_repr().to_bits().iter().rev() {
            if *bit {
                val += &cur;
            }
            cur.double_in_place();
        }

        result += &(val * power);
        power *= &base;
    }

    result
}

/// Obtain the limbs directly from a big int
pub fn get_limbs_representations_from_big_integer<SimulationF: PrimeField, ConstraintF: PrimeField>(
    elem: &<SimulationF as PrimeField>::BigInt,
) -> Vec<ConstraintF> {
    let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

    // push the lower limbs first
    let mut limbs: Vec<ConstraintF> = Vec::new();
    let mut cur = *elem;
    for _ in 0..params.num_limbs {
        let cur_bits = cur.to_bits(); // `to_bits` is big endian
        let cur_mod_r = <ConstraintF as PrimeField>::BigInt::from_bits(
            &cur_bits[cur_bits.len() - params.bits_per_limb..],
        ); // therefore, the lowest `bits_per_non_top_limb` bits is what we want.
        limbs.push(ConstraintF::from_repr(cur_mod_r));
        cur.divn(params.bits_per_limb as u32);
    }

    // then we reserve, so that the limbs are ``big limb first''
    limbs.reverse();

    limbs
}

/// Convert a `SimulationF` element into limbs (not constraints)
/// This is an internal function that would be reused by a number of other functions
pub fn get_limbs_representations<SimulationF: PrimeField, ConstraintF: PrimeField>(elem: &SimulationF) -> Vec<ConstraintF> {
    get_limbs_representations_from_big_integer::<SimulationF, ConstraintF>(&elem.into_repr())
}

pub fn limbs_to_bigint<ConstraintF: PrimeField>(
    bits_per_limb: usize,
    limbs: &[ConstraintF],
) -> BigUint {
    let mut val = BigUint::zero();
    let mut big_cur = BigUint::one();
    let two = BigUint::from(2u32);
    for limb in limbs.iter().rev() {
        let mut limb_repr = limb.into_repr().to_bits();
        limb_repr.reverse(); //We need them in little endian
        let mut small_cur = big_cur.clone();
        for limb_bit in limb_repr.iter() {
            if *limb_bit {
                val += &small_cur;
            }
            small_cur *= 2u32;
        }
        big_cur *= two.pow(bits_per_limb as u32);
    }

    val
}

pub fn bigint_to_constraint_field<ConstraintF: PrimeField>(bigint: &BigUint) -> ConstraintF {
    let mut val = ConstraintF::zero();
    let mut cur = ConstraintF::one();
    let bytes = bigint.to_bytes_be();

    let basefield_256 = ConstraintF::from_repr(<ConstraintF as PrimeField>::BigInt::from(256));

    for byte in bytes.iter().rev() {
        let bytes_basefield = ConstraintF::from(*byte as u128);
        val += cur * bytes_basefield;

        cur *= &basefield_256;
    }

    val
}