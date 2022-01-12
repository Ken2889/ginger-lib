#![allow(non_snake_case)]

use crate::iop::*;
use crate::iop::{Error, IOP};
use crate::Vec;
use algebra::{
    get_best_evaluation_domain, serialize::*, Evaluations as EvaluationsOnDomain, PrimeField,
    SemanticallyValid, ToBytes,
};
use derivative::Derivative;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, Index as VarIndex, SynthesisMode};

use crate::iop::sparse_linear_algebra::SparseMatrix;
use poly_commit::LabeledPolynomial;
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

impl<G1: Curve, G2: Curve> IndexInfo<G1, G2> {
    /// The maximum degree of polynomial required to represent this index in the
    /// the IOP.
    pub fn max_degree(&self, zk: bool) -> Result<usize, Error> {
        IOP::<G1, G2>::max_degree(self.num_constraints, self.num_witness + self.num_inputs, zk)
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

    // TODO: The matrix arithmetization polynomials are not needed directly. Only their commitments
    //  are actually used (acknowledged during circuit specific setup). We could restructure the
    //  code to avoid having them inside the Index.
    /// Arithmetization of the kernel-matrix product `R_A`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, and `val.row.col(X)` of it.
    pub a_star_arith: MatrixArithmetization<G1::ScalarField>,
    /// Arithmetization of the kernel-matrix product `R_B`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, and `val.row.col(X)` of it.
    pub b_star_arith: MatrixArithmetization<G1::ScalarField>,
    /// Arithmetization of the kernel-matrix product `R_C`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, and `val.row.col(X)` of it.
    pub c_star_arith: MatrixArithmetization<G1::ScalarField>,
}

impl<G1: Curve, G2: Curve> Index<G1, G2> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self, zk: bool) -> Result<usize, Error> {
        self.index_info.max_degree(zk)
    }

    /// Iterate over the indexed polynomials.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<G1::ScalarField>> {
        vec![
            &self.a_star_arith.row,
            &self.a_star_arith.col,
            &self.a_star_arith.val_row_col,
            &self.b_star_arith.row,
            &self.b_star_arith.col,
            &self.b_star_arith.val_row_col,
            &self.c_star_arith.row,
            &self.c_star_arith.col,
            &self.c_star_arith.val_row_col,
        ]
        .into_iter()
    }
}

impl<G1: Curve, G2: Curve> SemanticallyValid for Index<G1, G2> {
    fn is_valid(&self) -> bool {
        true
    }
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
        let (mut a, mut b, mut c) = post_process_matrices(&mut ics).expect("should not be `None`");
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

        let num_formatted_variables = ics.num_aux + ics.num_inputs;
        let num_constraints = ics.num_constraints;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h = get_best_evaluation_domain(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = get_best_evaluation_domain(num_non_zero(&mut ics))
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        // FFT domain for the public inputs, typically small
        let domain_x = get_best_evaluation_domain(ics.num_inputs)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let a_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let a_star_arith = arithmetize_matrix("a", &mut a, &domain_k, &domain_h, &domain_x)?;
        end_timer!(a_arithmetization_time);

        let b_arithmetization_time = start_timer!(|| "Arithmetizing B");
        let b_star_arith = arithmetize_matrix("b", &mut b, &domain_k, &domain_h, &domain_x)?;
        end_timer!(b_arithmetization_time);

        let c_arithmetization_time = start_timer!(|| "Arithmetizing C");
        let c_star_arith = arithmetize_matrix("c", &mut c, &domain_k, &domain_h, &domain_x)?;
        end_timer!(c_arithmetization_time);

        end_timer!(index_time);

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
            a_star_arith,
            b_star_arith,
            c_star_arith,
        })
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
/// Arithmetization of the circuit matrix. Only used to commit to the circuit during Fiat-Shamir
/// initialization.
pub struct MatrixArithmetization<F: PrimeField> {
    /// The polynomial for the row indices of `R_M`, in reduced form.
    pub row: LabeledPolynomial<F>,
    /// The polynomial for the column indices of `R_M`, in reduced form.
    pub col: LabeledPolynomial<F>,
    /// The reduced form of `val(X)*row(X)*col(X)`.
    pub val_row_col: LabeledPolynomial<F>,
}

pub(crate) fn arithmetize_matrix<F: PrimeField>(
    matrix_name: &str,
    // The R1CS matrix.
    matrix: &mut SparseMatrix<F>,
    // The indexer domain `K`.
    domain_k: &Box<dyn EvaluationDomain<F>>,
    // The domain `H` for the Lagrange representation of `M` .
    domain_h: &Box<dyn EvaluationDomain<F>>,
    // The input domain `X`, a subdomain of the Lagrange domain `H`.
    domain_x: &Box<dyn EvaluationDomain<F>>,
) -> Result<MatrixArithmetization<F>, Error> {
    let matrix_time = start_timer!(|| "Computing row, col, and val LDEs");

    let elems: Vec<_> = domain_h.elements().collect();

    let mut row_vec = Vec::new();
    let mut col_vec = Vec::new();
    let mut val_vec = Vec::new();

    let lde_evals_time = start_timer!(|| "Computing row, col and val evals");

    let mut count = 0;

    // As `R_M(X,Y) = R(X,X)*M(X,Y)`, we overall have `m(x,y) = M(x,y)/R(y,y)`.
    for (r, row) in matrix.into_iter().enumerate() {
        if !is_in_ascending_order(&row, |(_, a), (_, b)| a < b) {
            row.sort_by(|(_, a), (_, b)| a.cmp(b));
        };

        for &mut (val, i) in row {
            // As we do not re-index the y_A and y_B vectors by the input domain,
            // we simply take elems[r]
            let row_val = elems[r];
            // on the contrary, column vectors are re-indexed
            let col_val = elems[domain_h
                .reindex_by_subdomain(domain_x.size(), i)
                .map_err(|e| Error::Other(e.to_string()))?];

            row_vec.push(row_val);
            col_vec.push(col_val);
            val_vec.push(val);

            count += 1;
        }
    }

    end_timer!(lde_evals_time);

    // pad with zeroes
    for _ in 0..(domain_k.size() - count) {
        col_vec.push(elems[0]);
        row_vec.push(elems[0]);
        val_vec.push(F::zero());
    }
    let val_row_col_vec: Vec<_> = row_vec
        .par_iter()
        .zip(&col_vec)
        .zip(&val_vec)
        .map(|((row, col), val)| *row * col * val)
        .collect();

    let interpolate_time = start_timer!(|| "Interpolating on K");

    let row_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(row_vec, domain_k.clone());
    let col_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(col_vec, domain_k.clone());
    let val_row_col_evals_on_K =
        EvaluationsOnDomain::from_vec_and_domain(val_row_col_vec, domain_k.clone());

    let row = row_evals_on_K.clone().interpolate();
    let col = col_evals_on_K.clone().interpolate();
    let val_row_col = val_row_col_evals_on_K.interpolate();

    end_timer!(interpolate_time);

    end_timer!(matrix_time);

    let m_name = matrix_name.to_string();
    Ok(MatrixArithmetization {
        row: LabeledPolynomial::new(m_name.clone() + "_row", row, false),
        col: LabeledPolynomial::new(m_name.clone() + "_col", col, false),
        val_row_col: LabeledPolynomial::new(m_name.clone() + "_val_row_col", val_row_col, false),
    })
}

fn is_in_ascending_order<T: Ord>(x_s: &[T], is_less_than: impl Fn(&T, &T) -> bool) -> bool {
    if x_s.is_empty() {
        true
    } else {
        let mut i = 0;
        let mut is_sorted = true;
        while i < (x_s.len() - 1) {
            is_sorted &= is_less_than(&x_s[i], &x_s[i + 1]);
            i += 1;
        }
        is_sorted
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
