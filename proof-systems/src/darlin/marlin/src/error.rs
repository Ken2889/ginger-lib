use crate::iop::Error as IOPError;
use std::fmt::{Debug, Display};
use fiat_shamir::error::Error as FSError;

/// A `enum` specifying the possible failure modes of the `SNARK`.
#[derive(Debug)]
pub enum Error<E: Display + Debug> {
    /// The index is too large for the universal public parameters.
    IndexTooLarge,
    /// There was an error in the underlying holographic IOP.
    IOPError(IOPError),
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(E),
    /// There was an error in the underlying FS transform
    FiatShamirTransformError(FSError),
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
            Error::IOPError(err) => write!(f, "{}", err),
            Error::PolynomialCommitmentError(err) => write!(f, "{}", err),
            Error::FiatShamirTransformError(err) => write!(f, "{}", err),
            Error::Other(message) => write!(f, "{}", message),
        }
    }
}

impl<E: Display + Debug> From<IOPError> for Error<E> {
    fn from(err: IOPError) -> Self {
        Error::IOPError(err)
    }
}

impl<E: Display + Debug> From<FSError> for Error<E> {
    fn from(err: FSError) -> Self {
        Error::FiatShamirTransformError(err)
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
