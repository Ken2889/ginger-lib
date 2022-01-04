#![allow(non_snake_case)]

use crate::iop::*;
use crate::iop::{Error, IOP};
use crate::Vec;
use algebra::{get_best_evaluation_domain, serialize::*, PrimeField, SemanticallyValid, ToBytes};
use derivative::Derivative;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, Index as VarIndex, SynthesisMode};

use crate::iop::sparse_linear_algebra::SparseMatrix;
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
pub struct IndexInfo<F> {
    /// The total number of witnesses in the constraint system.
    pub num_witness: usize,
    /// The total number of public inputs in the constraint system.
    pub num_inputs: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The maximum number of non-zero entries in A,B,C.
    pub num_non_zero: usize,

    #[doc(hidden)]
    pub f: PhantomData<F>,
}

impl<F> ToBytes for IndexInfo<F> {
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

impl<F: PrimeField> IndexInfo<F> {
    /// The maximum degree of polynomial required to represent this index in the
    /// the IOP.
    pub fn max_degree(&self, zk: bool) -> Result<usize, Error> {
        IOP::<F>::max_degree(self.num_constraints, self.num_witness + self.num_inputs, zk)
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
pub struct Index<F: PrimeField> {
    /// Information about the index.
    pub index_info: IndexInfo<F>,

    /// The `A` matrix for the R1CS instance, in sparse representation.
    pub a: SparseMatrix<F>,
    /// The `B` matrix for the R1CS instance, in sparse representation.
    pub b: SparseMatrix<F>,
    /// The `C` matrix for the R1CS instance, in sparse representation
    pub c: SparseMatrix<F>,
}

impl<F: PrimeField> SemanticallyValid for Index<F> {
    fn is_valid(&self) -> bool {
        true
    }
}

impl<F: PrimeField> Index<F> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self, zk: bool) -> Result<usize, Error> {
        self.index_info.max_degree(zk)
    }
}

impl<F: PrimeField> IOP<F> {
    /// Generate the index for this constraint system, which essentially contains
    /// the indexer polynomials for the R1CS matrices.
    pub fn index<C: ConstraintSynthesizer<F>>(c: C) -> Result<Index<F>, Error> {
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

            f: PhantomData,
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

/*
    Elementary R1CS matrix conversion and post-processing.

*/

/// This function converts a R1CS matrix from ginger-lib into the sparse matrix representation
/// `Matrix` as used in this crate.
fn to_matrix_helper<F: PrimeField>(
    matrix: &[Vec<(F, VarIndex)>],
    num_input_variables: usize,
) -> SparseMatrix<F> {
    let mut new_matrix = Vec::with_capacity(matrix.len());
    let domain_x = get_best_evaluation_domain::<F>(num_input_variables).unwrap();
    let domain_x_size = domain_x.size();
    for row in matrix {
        let mut new_row = Vec::with_capacity(row.len());
        for (fe, column) in row {
            let column = match column {
                // public inputs correspond to the first columns
                VarIndex::Input(i) => *i,
                // private witnesses start right after
                VarIndex::Aux(i) => domain_x_size + i,
            };
            new_row.push((*fe, column))
        }
        new_matrix.push(new_row)
    }
    new_matrix
}

/// A simple function that balances the non-zero entries between A and B.
// TODO: write a test to check that `balance_matrices` improves the balancing of the matrices
// A and B by distributing the non-zero elements (more or less) evenly between the two.
fn balance_matrices<F: Field>(
    a_matrix: &mut Vec<Vec<(F, VarIndex)>>,
    b_matrix: &mut Vec<Vec<(F, VarIndex)>>,
) {
    let mut a_weight: usize = a_matrix.iter().map(|row| row.len()).sum();
    let mut b_weight: usize = b_matrix.iter().map(|row| row.len()).sum();
    for (a_row, b_row) in a_matrix.iter_mut().zip(b_matrix) {
        let a_row_weight = a_row.len();
        let b_row_weight = b_row.len();
        if (a_weight < b_weight && a_row_weight < b_row_weight)
            || (a_weight > b_weight && a_row_weight > b_row_weight)
        {
            std::mem::swap(a_row, b_row);
            a_weight = a_weight - a_row_weight + b_row_weight;
            b_weight = b_weight - b_row_weight + a_row_weight;
        }
    }
}

pub(crate) fn post_process_matrices<F: PrimeField>(
    cs: &mut ConstraintSystem<F>,
) -> Option<(SparseMatrix<F>, SparseMatrix<F>, SparseMatrix<F>)> {
    balance_matrices(&mut cs.at, &mut cs.bt);
    let a = to_matrix_helper(&cs.at, cs.num_inputs);
    let b = to_matrix_helper(&cs.bt, cs.num_inputs);
    let c = to_matrix_helper(&cs.ct, cs.num_inputs);
    Some((a, b, c))
}

pub(crate) fn num_non_zero<F: Field>(cs: &mut ConstraintSystem<F>) -> usize {
    let a_non_zeros = cs.at.iter().map(|row| row.len()).sum();
    let b_non_zeros = cs.bt.iter().map(|row| row.len()).sum();
    let c_non_zeros = cs.ct.iter().map(|row| row.len()).sum();

    let max = *[a_non_zeros, b_non_zeros, c_non_zeros]
        .iter()
        .max()
        .expect("iterator is not empty");
    max
}
