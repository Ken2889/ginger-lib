use crate::ahp::Error as AHPError;
use std::fmt::{Debug, Display};

/// A `enum` specifying the possible failure modes of the `SNARK`.
#[derive(Debug)]
pub enum Error<E: Display + Debug> {
    /// The index is too large for the universal public parameters.
    IndexTooLarge,
    /// There was an error in the underlying holographic IOP.
    AHPError(AHPError),
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(E),
    /// Other error
    Other(String),
}

impl<E: Display + Debug> Display for Error<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IndexTooLarge => write!(
                f,
                "The index is too large for the universal public parameters"
            ),
            Error::AHPError(err) => write!(f, "{}", err),
            Error::PolynomialCommitmentError(err) => write!(f, "{}", err),
            Error::Other(message) => write!(f, "{}", message),
        }
    }
}

impl<E: Display + Debug> From<AHPError> for Error<E> {
    fn from(err: AHPError) -> Self {
        Error::AHPError(err)
    }
}

impl<E: Display + Debug> Error<E> {
    /// Convert an error in the underlying polynomial commitment scheme
    /// to a `Error`.
    pub fn from_pc_err(err: E) -> Self {
        Error::PolynomialCommitmentError(err)
    }
}

impl<E: Display + Debug> std::error::Error for Error<E> {}
