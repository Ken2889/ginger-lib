//! A module for simulating group arithmetics over non-native fields.
pub mod short_weierstrass;
pub use self::short_weierstrass::*;

#[cfg(test)]
mod tests;
