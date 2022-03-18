<h1 align="center">Coboundary Marlin</h1>

`marlin` is a Rust crate that implements *Coboundary Marlin*, an optimization of the [Marlin](https://eprint.iacr.org/2019/1047) preprocessing zk-SNARK for rank-one constraint systems (R1CS). The crate is based on a fork from [arkworks](http://github.com/arkworks-rs/marlin), using the modifications as described in [HGB](https://eprint.iacr.org/2021/930). 

## On the argument system ##

Coboundary Marlin is a zk-SNARK for R1CS. It is built on top of any homomorphic polynomial commitment scheme, proving the satisfiability of a given constraint system (subject to some public inputs) by means of an algebraic oracle protocol.  

The main differences to Marlin are as follows:

- A cohomological sumcheck argument, which allows a more light-weight zero-knowledge randomization and drops the need for proving individual degree bounds,
- a different arithmetization of the R1CS matrices, which is directly based on their Lagrange representation.

See [HGB](https://eprint.iacr.org/2021/930) for details. 

##  Directory structure ##

The high-level structure of the repository is as follows:

- [`data_structures.rs`](src/data_structures.rs) essentially defines the structures around key material and SNARK proofs.
- [`lib.rs`](src/lib.rs) contains the functions for parameter generation, producing and verifying SNARK proofs. The latter two are obtained as Fiat-Shamir transform of the interactive oracle proof as given in the submodule `iop`, replacing oracles by their commitments.
- [`iop`](src/iop/mod.rs) contains the "algebraic oracle proof", i.e. a pre-compiled version of the interactive protocol, in which polynomials to be sent to the verifier are left uncommitted. The module consists of
  - [`indexer.rs`](src/iop/indexer.rs), which contains structs and functions for the circuit-specific pre-processing stage. 
  - [`prover.rs`](src/iop/prover.rs)  and [`verifier.rs`](src/iop/verifier.rs), which implement the round functions of prover and verifier of the oracle proof.