macro_rules! bigint_impl {
    ($name:ident, $num_limbs:expr) => {
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Default, Hash, Serialize, Deserialize)]
        #[serde(transparent)]
        pub struct $name(pub [u64; $num_limbs]);

        impl $name {
            pub fn new(value: [u64; $num_limbs]) -> Self {
                $name(value)
            }

            #[inline]
            fn to_bytes_le(&self) -> Vec<u8> {
                let array_map = self.0.iter().map(|limb| limb.to_le_bytes());
                let mut res = Vec::<u8>::with_capacity($num_limbs * 8);
                for limb in array_map {
                    res.extend_from_slice(&limb);
                }
                res
            }
        }

        impl BigInteger for $name {
            #[inline]
            fn add_nocarry(&mut self, other: &Self) -> bool {
                let mut carry = 0;

                for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
                    *a = arithmetic::adc(*a, *b, &mut carry);
                }

                carry != 0
            }

            #[inline]
            fn sub_noborrow(&mut self, other: &Self) -> bool {
                let mut borrow = 0;

                for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
                    *a = arithmetic::sbb(*a, *b, &mut borrow);
                }

                borrow != 0
            }

            #[inline]
            fn mul2(&mut self) {
                let mut last = 0;
                for i in &mut self.0 {
                    let tmp = *i >> 63;
                    *i <<= 1;
                    *i |= last;
                    last = tmp;
                }
            }

            #[inline]
            fn muln(&mut self, mut n: u32) {
                if n >= 64 * $num_limbs {
                    *self = Self::from(0);
                    return;
                }

                while n >= 64 {
                    let mut t = 0;
                    for i in &mut self.0 {
                        ::std::mem::swap(&mut t, i);
                    }
                    n -= 64;
                }

                if n > 0 {
                    let mut t = 0;
                    for i in &mut self.0 {
                        let t2 = *i >> (64 - n);
                        *i <<= n;
                        *i |= t;
                        t = t2;
                    }
                }
            }

            #[inline]
            fn div2(&mut self) {
                let mut t = 0;
                for i in self.0.iter_mut().rev() {
                    let t2 = *i << 63;
                    *i >>= 1;
                    *i |= t;
                    t = t2;
                }
            }

            #[inline]
            fn divn(&mut self, mut n: u32) {
                if n >= 64 * $num_limbs {
                    *self = Self::from(0);
                    return;
                }

                while n >= 64 {
                    let mut t = 0;
                    for i in self.0.iter_mut().rev() {
                        ::std::mem::swap(&mut t, i);
                    }
                    n -= 64;
                }

                if n > 0 {
                    let mut t = 0;
                    for i in self.0.iter_mut().rev() {
                        let t2 = *i << (64 - n);
                        *i >>= n;
                        *i |= t;
                        t = t2;
                    }
                }
            }

            #[inline]
            fn is_odd(&self) -> bool {
                self.0[0] & 1 == 1
            }

            #[inline]
            fn is_even(&self) -> bool {
                !self.is_odd()
            }

            #[inline]
            fn is_zero(&self) -> bool {
                self.0.iter().all(|&e| e == 0)
            }

            #[inline]
            fn num_bits(&self) -> u32 {
                let mut ret = $num_limbs * 64;
                for i in self.0.iter().rev() {
                    let leading = i.leading_zeros();
                    ret -= leading;
                    if leading != 64 {
                        break;
                    }
                }

                ret
            }

            #[inline]
            fn get_bit(&self, i: usize) -> bool {
                if i >= 64 * $num_limbs {
                    false
                } else {
                    let limb = i / 64;
                    let bit = i - (64 * limb);
                    (self.0[limb] & (1 << bit)) != 0
                }
            }

            // Defines a BigInt from a slice of big endian booleans.
            #[inline]
            fn from_bits(bits: &[bool]) -> Self {
                let mut res = Self::default();
                let mut acc: u64 = 0;

                // convert to little endian as the limbs are in
                // little endian order
                let mut bits = bits.to_vec();
                bits.reverse();
                for (i, bits64) in bits.chunks(64).enumerate() {
                    // each chunk is again arranged big endian
                    for bit in bits64.iter().rev() {
                        acc <<= 1;
                        acc += *bit as u64;
                    }
                    res.0[i] = acc;
                    acc = 0;
                }
                res
            }

            // Note: Does not skip leading zeroes
            #[inline]
            fn to_bits(&self) -> Vec<bool> {
                let mut res = Vec::with_capacity(256);
                for b in BitIterator::new(self.0) {
                    res.push(b);
                }
                res
            }

            #[inline]
            fn find_wnaf(&self) -> Vec<i64> {
                let mut res = vec![];

                let mut e = self.clone();
                while !e.is_zero() {
                    let z: i64;
                    if e.is_odd() {
                        z = 2 - (e.0[0] % 4) as i64;
                        if z >= 0 {
                            e.sub_noborrow(&Self::from(z as u64));
                        } else {
                            e.add_nocarry(&Self::from((-z) as u64));
                        }
                    } else {
                        z = 0;
                    }
                    res.push(z);
                    e.div2();
                }

                res
            }
        }

        impl CanonicalSerialize for $name {
            #[inline]
            fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
                self.write(writer)?;
                Ok(())
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                $num_limbs * 8
            }
        }

        impl CanonicalDeserialize for $name {
            #[inline]
            fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
                let value = Self::read(reader)?;
                Ok(value)
            }
        }

        impl ToBytes for $name {
            #[inline]
            fn write<W: Write>(&self, writer: W) -> IoResult<()> {
                self.0.write(writer)
            }
        }

        impl FromBytes for $name {
            #[inline]
            fn read<R: Read>(reader: R) -> IoResult<Self> {
                <[u64; $num_limbs]>::read(reader).map(Self::new)
            }
        }

        impl Display for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                for i in self.0.iter().rev() {
                    write!(f, "{:016X}", *i)?;
                }
                Ok(())
            }
        }

        impl Ord for $name {
            #[inline]
            fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
                for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
                    if a < b {
                        return ::std::cmp::Ordering::Less;
                    } else if a > b {
                        return ::std::cmp::Ordering::Greater;
                    }
                }

                ::std::cmp::Ordering::Equal
            }
        }

        impl PartialOrd for $name {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Distribution<$name> for Standard {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $name {
                $name(rng.gen())
            }
        }

        impl AsMut<[u64]> for $name {
            #[inline]
            fn as_mut(&mut self) -> &mut [u64] {
                &mut self.0
            }
        }

        impl AsRef<[u64]> for $name {
            #[inline]
            fn as_ref(&self) -> &[u64] {
                &self.0
            }
        }

        impl From<u64> for $name {
            #[inline]
            fn from(val: u64) -> $name {
                let mut repr = Self::default();
                repr.0[0] = val;
                repr
            }
        }

        impl TryFrom<BigUint> for $name {
            type Error = Box<dyn std::error::Error>;

            #[inline]
            fn try_from(val: BigUint) -> Result<$name, Self::Error> {
                let bytes = val.to_bytes_le();

                if bytes.len() > $num_limbs * 8 {
                    Err(format!(
                        "A BigUint of {} bytes cannot fit into a BigInt of {} bytes.",
                        bytes.len(),
                        $num_limbs * 8
                    ))?
                } else {
                    let mut limbs = [0u64; $num_limbs];

                    bytes
                        .chunks(8)
                        .into_iter()
                        .enumerate()
                        .for_each(|(i, chunk)| {
                            let mut chunk_padded = [0u8; 8];
                            chunk_padded[..chunk.len()].copy_from_slice(chunk);
                            limbs[i] = u64::from_le_bytes(chunk_padded)
                        });

                    Ok(Self(limbs))
                }
            }
        }

        impl From<$name> for BigUint {
            #[inline]
            fn from(val: $name) -> BigUint {
                BigUint::from_bytes_le(&val.to_bytes_le())
            }
        }
    };
}
