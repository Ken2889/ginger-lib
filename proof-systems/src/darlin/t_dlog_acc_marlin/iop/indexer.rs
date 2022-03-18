#![allow(non_snake_case)]

use algebra::{serialize::*, Curve, ToBytes};
use derivative::Derivative;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisMode};

use crate::darlin::t_dlog_acc_marlin::iop::IOP;
use marlin::iop::indexer::{num_non_zero, post_process_matrices};
use marlin::iop::sparse_linear_algebra::SparseMatrix;
use marlin::iop::Error;
use std::marker::PhantomData;

/// Information about the index, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Copy(bound = ""),
    Default(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexInfo<G1: Curve, G2: Curve> {
    /// The total number of witnesses in the constraint system.
    pub num_witness: usize,
    /// The total number of public inputs in the constraint system.
    pub num_inputs: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The maximum number of non-zero entries in A,B,C.
    pub num_non_zero: usize,

    #[doc(hidden)]
    pub g1: PhantomData<G1>,
    #[doc(hidden)]
    pub g2: PhantomData<G2>,
}

impl<G1: Curve, G2: Curve> ToBytes for IndexInfo<G1, G2> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> std::io::Result<()> {
        self.num_witness
            .serialize_without_metadata(&mut writer)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", e)))?;
        self.num_inputs
            .serialize_without_metadata(&mut writer)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", e)))?;
        self.num_constraints
            .serialize_without_metadata(&mut writer)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", e)))?;
        self.num_non_zero
            .serialize_without_metadata(&mut writer)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", e)))?;
        Ok(())
    }
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
/// The "indexed" version of the constraint system.
/// Besides auxiliary information on the index, contains the R1CS matrices `M=A,B,C`.
pub struct Index<G1: Curve, G2: Curve> {
    /// Information about the index.
    pub index_info: IndexInfo<G1, G2>,

    /// The `A` matrix for the R1CS instance, in sparse representation.
    pub a: SparseMatrix<G1::ScalarField>,
    /// The `B` matrix for the R1CS instance, in sparse representation.
    pub b: SparseMatrix<G1::ScalarField>,
    /// The `C` matrix for the R1CS instance, in sparse representation
    pub c: SparseMatrix<G1::ScalarField>,
}

impl<G1: Curve, G2: Curve> IOP<G1, G2> {
    /// Generate the index for this constraint system, which essentially contains
    /// the indexer polynomials for the R1CS matrices.
    pub fn index<C: ConstraintSynthesizer<G1::ScalarField>>(c: C) -> Result<Index<G1, G2>, Error> {
        let index_time = start_timer!(|| "IOP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let mut ics = ConstraintSystem::new(SynthesisMode::Setup);
        c.generate_constraints(&mut ics)?;
        end_timer!(constraint_time);

        // matrix post-processing: balance matrices
        let matrix_processing_time = start_timer!(|| "Processing matrices");
        let (a, b, c) = post_process_matrices(&mut ics).expect("should not be `None`");
        add_to_trace!(|| "number of (formatted) input_variables", || format!(
            "{}",
            ics.num_inputs
        ));
        add_to_trace!(|| "number of witness_variables", || format!(
            "{}",
            ics.num_aux
        ));
        add_to_trace!(|| "number of num_constraints", || format!(
            "{}",
            ics.num_constraints
        ));
        add_to_trace!(|| "number of num_non_zero", || format!(
            "{}",
            num_non_zero(&mut ics)
        ));
        end_timer!(matrix_processing_time);

        let index_info = IndexInfo {
            num_witness: ics.num_aux,
            num_inputs: ics.num_inputs,
            num_constraints: ics.num_constraints,
            num_non_zero: num_non_zero(&mut ics),
            g1: PhantomData,
            g2: PhantomData,
        };

        end_timer!(index_time);
        Ok(Index {
            index_info,
            a,
            b,
            c,
        })
    }
}
