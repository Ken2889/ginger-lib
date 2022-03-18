<h1 align="center">poly-commit: Linear polynomial commitment schemes</h1>

[`poly-commit`](src/lib.rs) is a Rust crate for homomorphic (univariate) polynomial commitment schemes. It provides general traits and functions for linear polynomial commitments,  including domain extension beyond the size of the committer key. 

As concrete scheme we provide the [BCMS](https://eprint.iacr.org/2020/499) variant of  the *dlog polynomial commitment scheme* from [Bootle et al., 2016](https://eprint.iacr.org/2016/263). This is the scheme we use in our recursive Darlin SNARK from [HGB](https://eprint.iacr.org/2021/930).

The crate is forked from [arkworks](https://github.com/arkworks-rs/poly-commit), restructured and adapted to the needs of our [Darlin protocol suite](https://github.com/HorizenLabs/ginger-lib).

## Directory Structure

The high-level overview of the crate is as follows.

- [`lib.rs`](src/lib.rs) bundles all the modules listed below. It contains the trait for linear polynomial commitment schemes, which provides the interfaces for atomic and more expressive opening queries, including the recursion-friendly feature of splitting the verifiers into a succinct and a non-succinct (or "hard") part. We give default implementations for: 
  - single point queries on several polynomials (by using the standard technique),
  - multi-point queries on one or several polynomials, using the "batch evaluation proof" from [HaloInfinite](https://eprint.iacr.org/2020/1536)). 
- [`domain_extended`](src/domain_extended/mod.rs) generically handles the extension of any linear polynomial commitment scheme beyond the size of its committer key.
- [`ipa_pc`](src/ipa_pc/mod.rs) implements the dlog polynomial commitment scheme as described in [BCMS](https://eprint.iacr.org/2020/499). It moreover provides a batch verifier as well as related functions (such as a separate aggregation prover for the "hard" parts of the dlog verifier).