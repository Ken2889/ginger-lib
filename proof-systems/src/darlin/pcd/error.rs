#[derive(Debug)]
pub enum PCDError {
    SchemeSetupError(String),
    NodeSetupError(String),
    CreationFailure(String),
    FailedSuccinctVerification(String),
    FailedHardVerification(String),
    MissingSystemInputs(String),
    MissingUserInputs(String),
    Other(String),
}

impl std::fmt::Display for PCDError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCDError::SchemeSetupError(err) => {
                write!(f, "Failed to bootstrap the PCDScheme: {}", err)
            }
            PCDError::NodeSetupError(err) => {
                write!(f, "Failed to bootstrap the PCDNode: {}", err)
            }
            PCDError::CreationFailure(err) => {
                write!(f, "Failed to create PCD: {}", err)
            }
            PCDError::FailedSuccinctVerification(err) => {
                write!(f, "Succinct check failed: {}", err)
            }
            PCDError::FailedHardVerification(err) => write!(f, "Hard check failed: {}", err),
            PCDError::MissingSystemInputs(missing_field) => {
                write!(f, "Unable to retrieve system input: {}", missing_field)
            }
            PCDError::MissingUserInputs(missing_field) => {
                write!(f, "Unable to retrieve user input: {}", missing_field)
            }
            PCDError::Other(err) => write!(f, "PCD Error: {}", err),
        }
    }
}

impl std::error::Error for PCDError {}
