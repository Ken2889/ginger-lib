//! The module for our Darlin proof carrying data (PCD) scheme as described in
//! our [DarlinProofTree doc](TODO: link).
//! The Darlin PCD scheme is based on (a variant of) Marlin/dlog, aggregating
//! the dlog "hard parts" as well as the inner sumchecks across multiple
//! circuits.
//! The modules is split into the following submodules
//!     - `accumulators`: accumulator structs and their aggregation schemes as
//!     stand-alone non-interactive arguments. Although the stand-alone NI arguments
//!     are not applied in recursion, they are useful for post-processing.
//!     - `pcd`: Proof carrying data trait and data structures.
//!     - `proof_aggregator`: utilities for proof post-processing, such as batch
//!     verification and aggregation of their dlog hard parts.
pub mod accumulators;
pub mod pcd;
pub mod proof_aggregator;
pub mod tests;

use poly_commit::{DomainExtendedPolynomialCommitment, ipa_pc::InnerProductArgPC};

pub(crate) type DomainExtendedIpaPc<G, FS> = DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, FS>>;