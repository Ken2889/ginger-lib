use std::{
    cmp::{Ord, Ordering, PartialOrd},
    fmt::{Display, Formatter, Result as FmtResult},
    marker::PhantomData,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    str::FromStr,
};
use unroll::unroll_for_loops;

use crate::{
    biginteger::{
        arithmetic as fa, BigInteger as _BigInteger, BigInteger256, BigInteger320, BigInteger384,
        BigInteger768, BigInteger832,
    },
    bytes::{FromBytes, ToBytes},
    groups::Group,
    fields::{
        Field, FpParameters, LegendreSymbol, MulShort, MulShortAssign, PrimeField, SquareRootField,
    },
    serialize::{
        buffer_byte_size, CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
        CanonicalSerializeWithFlags, EmptyFlags, Flags, SerializationError,
    },
    SemanticallyValid,
};

use serde::{Deserialize, Serialize};
use std::io::{Error as IoError, ErrorKind, Read, Result as IoResult, Write};

#[cfg(use_asm)]
use std::mem::MaybeUninit;

#[cfg(use_asm)]
include!(concat!(env!("OUT_DIR"), "/field_assembly.rs"));

impl_Fp!(Fp256, Fp256Parameters, BigInteger256, BigInteger256, 4);
impl_Fp!(Fp320, Fp320Parameters, BigInteger320, BigInteger320, 5);
impl_Fp!(Fp384, Fp384Parameters, BigInteger384, BigInteger384, 6);
impl_Fp!(Fp768, Fp768Parameters, BigInteger768, BigInteger768, 12);
impl_Fp!(Fp832, Fp832Parameters, BigInteger832, BigInteger832, 13);
