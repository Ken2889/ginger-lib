use crate::Error;
use algebra::{
    bytes::{FromBytes, ToBytes},
    Field, FromBytesChecked, UniformRand,
};
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::hash::Hash;

pub mod schnorr;

pub trait FieldBasedSignatureScheme {
    type Data: Field;
    type PublicKey: FromBytes
        + FromBytesChecked
        + ToBytes
        + Hash
        + Eq
        + Copy
        + Clone
        + Default
        + Debug
        + Send
        + Sync
        + UniformRand
        + Serialize
        + for<'a> Deserialize<'a>;
    type SecretKey: ToBytes + Clone + Default + Serialize + for<'a> Deserialize<'a>;
    type Signature: Copy
        + Clone
        + Default
        + Send
        + Sync
        + Debug
        + Eq
        + PartialEq
        + ToBytes
        + FromBytes
        + FromBytesChecked
        + Serialize
        + for<'a> Deserialize<'a>;

    fn keygen<R: Rng>(rng: &mut R) -> (Self::PublicKey, Self::SecretKey);

    fn get_public_key(sk: &Self::SecretKey) -> Self::PublicKey;

    fn sign<R: Rng>(
        rng: &mut R,
        pk: &Self::PublicKey,
        sk: &Self::SecretKey,
        message: Self::Data,
    ) -> Result<Self::Signature, Error>;

    fn verify(
        pk: &Self::PublicKey,
        message: Self::Data,
        signature: &Self::Signature,
    ) -> Result<bool, Error>;

    fn keyverify(pk: &Self::PublicKey) -> bool;
}
