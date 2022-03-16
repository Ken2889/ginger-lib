/// The error type for `FiatShamirRngSeed` and `FiatShamirRng`.
#[derive(Debug)]
pub enum Error {
    /// FiatShamirRNG was initialized passing uncorrect data
    BadFiatShamirInitialization(String),

    /// Error while absorbing data
    RecordError(String),

    /// Error while squeezing data
    GetChallengeError(String),

    /// Other errors
    Other(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::BadFiatShamirInitialization(e) => {
                write!(f, "Failed to compute seed for FiatShamir RNG: {}", e)
            }
            Error::RecordError(e) => write!(f, "Unable to record data: {}", e),
            Error::GetChallengeError(e) => write!(f, "Unable to get challenge(s): {}", e),
            Error::Other(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for Error {}
