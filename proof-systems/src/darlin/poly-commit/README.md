<h1 align="center">poly-commit: the dlog polynomial commitment scheme</h1>

<p align="center">
    <a href= "https://github.com/HorizenOfficial/HorizenLabs/poly-commit/releases"><img src="https://img.shields.io/github/release/HorizenLabs/poly-commit.svg"></a>
    <a href="AUTHORS"><img src="https://img.shields.io/github/contributors/HorizenLabs/poly-commit.svg?"></a>
    <a href="https://travis-ci.com/github/HorizenLabs/poly-commit"><img src="https://app.travis-ci.com/HorizenLabs/poly-commit.svg?branch=master"></a>
    <a href="LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="CONTRIBUTING.md"><img src="https://img.shields.io/badge/PRs-welcome-brightgreen.svg?style=flat-square"></a>
</p>

[`poly-commit`](src/lib.rs) is a Rust library for univariate polynomial commitment schemes. It provides general traits and functions for polynomial commitments.
As concrete scheme we provide the [BCMS](https://eprint.iacr.org/2020/499) variant of  the *dlog polynomial commitment scheme* from [Bootle et al., 2016](https://eprint.iacr.org/2016/263), including 

- the "batch evaluation proof" for multi-point queries from [HaloInfinite](https://eprint.iacr.org/2020/1536), and
- domain extension beyond the size of the committer key.  

This is the scheme we use in our recursive Darlin SNARK from [HGB](https://eprint.iacr.org/2021/930). The library is forked from [arkworks](https://github.com/arkworks-rs/poly-commit), restructured and adapted to the needs of our [Darlin protocol suite](https://github.com/HorizenLabs/ginger-lib).

## Directory Structure

- [`data_structures`](src/data_structures.rs) essentially contains the data structures and related traits for key material and evaluation proofs.
- [`lib.rs`](src/lib.rs) contains the main trait for a polynomial commitment scheme. The trait serves the interfaces for atomic and more expressive opening queries such as multi-point multi-polynomial queries.  
- [`rng`](src/rng.rs) provides a trait for sponge-like pseudo random number generators, tailored to Fiat-Shamir transform usage, and an implementation using the ChaCha20-based random number generator from [rand_chacha](https://crates.io/crates/rand_chacha). 
- [`ipa_pc`](src/ipa_pc/mod.rs) gives the implementation the dlog polynomial commitment scheme in the style of  [BCMS](https://eprint.iacr.org/2020/499). We further implement the above mentioned batch evaluation proof and domain extension.
It moreover contains functions related to proof recursion (such as the *succinct* and *non-succinct verifier*).

## Release note

The upcoming release (see [`refactor_pc_dev`](https://github.com/HorizenLabs/poly-commit/tree/refactor_pc_dev)) will involve a complete restructuring of the current release. It narrows down the trait for general polynomial commitment schemes to linear ones, handling both more expressive opening queries as well as domain extension by default implementations.

## Build instructions

The library compiles on the `1.51.0 stable` toolchain of the Rust compiler. 
```bash
git clone https://github.com/HorizenLabs/poly-commit.git
cd poly-commit
cargo build --release
```
Run tests using
```bash
cargo test --all-features 
```
More detailed information can be found in our [build guide](BUILD.md).
