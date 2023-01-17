<h1 align="center">Coboundary Marlin</h1>

<p align="center">
    <a href= "https://github.com/HorizenLabs/marlin/releases"><img src="https://img.shields.io/github/release/HorizenLabs/marlin.svg"></a>
    <a href="AUTHORS"><img src="https://img.shields.io/github/contributors/HorizenLabs/marlin.svg?"></a>
    <a href="https://travis-ci.com/github/HorizenLabs/marlin"><img src="https://app.travis-ci.com/HorizenLabs/marlin.svg?branch=master"></a>
    <a href="LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="CONTRIBUTING.md"><img src="https://img.shields.io/badge/PRs-welcome-brightgreen.svg?style=flat-square"></a>
</p>

[`marlin`](HL_marlin) is a Rust library that implements *Coboundary Marlin*, an optimization of the [Marlin](https://eprint.iacr.org/2019/1047) preprocessing zk-SNARK for rank-one constraint systems (R1CS). The library is based on a fork from [arkworks](http://github.com/arkworks-rs/marlin), using the modifications as described in [HGB](https://eprint.iacr.org/2021/930). 

## On the argument system

Coboundary Marlin is a zk-SNARK for R1CS as used by [`ginger-lib`](https://github.com/HorizenOfficial/ginger-lib"). It is built on top of any homomorphic polynomial commitment scheme, proving the satisfiability of a given constraint system (subject to some  public inputs) by means of an algebraic oracle protocol. The main differences to Marlin are as follows:

- A cohomological sumcheck argument, which allows a more light-weight zero-knowledge randomization and drops the need for proving individual degree bounds,
- a different arithmetization of the R1CS matrices, which is directly based on their Lagrange representation.

See [HGB](https://eprint.iacr.org/2021/930) for details. 

##  Directory structure 

The high-level structure of the repository is as follows:

- [`data_structures.rs`](src/data_structures.rs) defines the structs for key material and SNARK proofs.
- [`lib.rs`](src/lib.rs) contains the public SNARK functions: Parameter generation, producing and verifying proofs. The latter two are obtained by a Fiat-Shamir transform of the interactive oracle proof contained in [`ahp`](src/ahp/mod.rs) (and replacing oracles by commitments).
- [`ahp`](src/ahp/mod.rs) contains the algebraic oracle proof, i.e. a pre-compiled version of the interactive protocol, in which polynomials to be sent to the verifier are left uncommitted. The module consists of
  - [`constraint_systems`](src/ahp/constraint_systems.rs), which contains extensions of the constraint system trait as supported by the current version of [`ginger-lib`](https://github.com/HorizenOfficial/ginger-lib"),
  - [`indexer`](src/ahp/indexer.rs), which provides structs and functions for the circuit-specific pre-processing stage,
  - [`prover`](src/ahp/prover.rs)  and [`verifier`](src/ahp/verifier.rs), which implements the round functions of prover and verifier of the oracle proof.

## Release Note

The current release implements Coboundary Marlin using Marlin's original matrix arithmetization.

## Build instructions

The library compiles on the `1.51.0 stable` toolchain of the Rust compiler. 
```bash
git clone https://github.com/HorizenLabs/marlin.git
cd marlin
cargo build --release
```
Run tests using
```bash
cargo test --all-features 
```
More detailed information can be found in our [build guide](BUILD.md).
