#![allow(non_snake_case)]

use crate::ahp::indexer::Matrix;
use crate::ahp::*;
use crate::{BTreeMap, ToString};
use algebra::{get_best_evaluation_domain, EvaluationDomain, Evaluations as EvaluationsOnDomain};
use algebra::{serialize::*, Field, PrimeField};
use derivative::Derivative;
use poly_commit::LabeledPolynomial;
use r1cs_core::{ConstraintSystem, ConstraintSystemAbstract, Index as VarIndex};

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

// This function converts a matrix output by Zexe's constraint infrastructure
// to the one used in this crate.
fn to_matrix_helper<F: Field>(
    matrix: &[Vec<(F, VarIndex)>],
    num_input_variables: usize,
) -> Matrix<F> {
    let mut new_matrix = Vec::with_capacity(matrix.len());
    for row in matrix {
        let mut new_row = Vec::with_capacity(row.len());
        for (fe, column) in row {
            let column = match column {
                VarIndex::Input(i) => *i,
                VarIndex::Aux(i) => num_input_variables + i,
            };
            new_row.push((*fe, column))
        }
        new_matrix.push(new_row)
    }
    new_matrix
}

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

pub(crate) fn pad_input<F: PrimeField, CS: ConstraintSystemAbstract<F>>(
    cs: &mut CS,
    formatted_input_size: usize,
) {
    let domain_x = get_best_evaluation_domain::<F>(formatted_input_size);
    assert!(domain_x.is_some());

    let padded_size = domain_x.unwrap().size();

    if padded_size > formatted_input_size {
        for i in 0..(padded_size - formatted_input_size) {
            cs.alloc_input(|| format!("padding input {}", i), || Ok(F::zero()))
                .unwrap();
        }
    }
}

pub(crate) fn process_matrices<F: Field>(
    cs: &mut ConstraintSystem<F>,
) -> Option<(Matrix<F>, Matrix<F>, Matrix<F>)> {
    balance_matrices(&mut cs.at, &mut cs.bt);
    let a = to_matrix_helper(&cs.at, cs.num_inputs);
    let b = to_matrix_helper(&cs.bt, cs.num_inputs);
    let c = to_matrix_helper(&cs.ct, cs.num_inputs);
    Some((a, b, c))
}

pub(crate) fn num_non_zero<F: Field>(cs: &mut ConstraintSystem<F>) -> usize {
    let a_density = cs.at.iter().map(|row| row.len()).sum();
    let b_density = cs.bt.iter().map(|row| row.len()).sum();
    let c_density = cs.ct.iter().map(|row| row.len()).sum();

    let max = *[a_density, b_density, c_density]
        .iter()
        .max()
        .expect("iterator is not empty");
    max
}

pub(crate) fn make_matrices_square<F: Field>(cs: &mut ConstraintSystem<F>) {
    let num_variables = cs.num_inputs + cs.num_aux;
    let num_constraints = cs.num_constraints();

    let matrix_dim = padded_matrix_dim(num_variables, num_constraints);
    let nnz = num_non_zero(cs);

    let matrix_padding = ((num_variables as isize) - (num_constraints as isize)).abs();
    if num_variables > num_constraints {
        use std::convert::identity as iden;
        // Add dummy constraints of the form 0 * 0 == 0
        for i in 0..matrix_padding {
            cs.enforce(|| format!("pad constraint {}", i), iden, iden, iden);
        }
    } else {
        // Add dummy unconstrained variables
        for i in 0..matrix_padding {
            let _ = cs
                .alloc(|| format!("pad var {}", i), || Ok(F::one()))
                .expect("alloc failed");
        }
    }
    assert_eq!(
        cs.num_inputs + cs.num_aux,
        cs.num_constraints,
        "padding failed!"
    );
    assert_eq!(
        cs.num_inputs + cs.num_aux,
        matrix_dim,
        "padding does not result in expected matrix size!"
    );
    assert_eq!(num_non_zero(cs), nnz, "padding changed matrix density");
}

/// Formats the public input according to the requirements of the constraint
/// system
pub(crate) fn format_public_input<F: Field>(public_input: &[F]) -> Vec<F> {
    let mut input = vec![F::one()];
    input.extend_from_slice(public_input);
    input
}

/// Takes in a previously formatted public input and removes the formatting
/// imposed by the constraint system.
pub(crate) fn unformat_public_input<F: Field>(input: &[F]) -> Vec<F> {
    input[1..].to_vec()
}

/// This must *always* be in sync with `make_matrices_square`.
pub(crate) fn padded_matrix_dim(num_formatted_variables: usize, num_constraints: usize) -> usize {
    std::cmp::max(num_formatted_variables, num_constraints)
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct MatrixEvals<F: PrimeField> {
    /// Evaluations of the LDE of row.
    pub row: EvaluationsOnDomain<F>,
    /// Evaluations of the LDE of col.
    pub col: EvaluationsOnDomain<F>,
    /// Evaluations of the LDE of val.
    pub val: EvaluationsOnDomain<F>,
}

/// Contains information about the arithmetization of the matrix M^*.
/// Here `M^*(i, j) := M(j, i) * u_H(j, j)`. For more details, see [COS19].
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct MatrixArithmetization<F: PrimeField> {
    /// LDE of the row indices of M^*.
    pub row: LabeledPolynomial<F>,
    /// LDE of the column indices of M^*.
    pub col: LabeledPolynomial<F>,
    /// LDE of the non-zero entries of M^*.
    pub val: LabeledPolynomial<F>,
    /// LDE of the vector containing entry-wise products of `row` and `col`,
    /// where `row` and `col` are as above.
    pub row_col: LabeledPolynomial<F>,

    /// Evaluation of `self.row`, `self.col`, and `self.val` on the domain `K`.
    pub evals_on_K: MatrixEvals<F>,

    /// Evaluation of `self.row`, `self.col`, and, `self.val` on
    /// an extended domain B (of size > `3K`).
    // TODO: rename B everywhere.
    pub evals_on_B: MatrixEvals<F>,

    /// Evaluation of `self.row_col` on an extended domain B (of size > `3K`).
    pub row_col_evals_on_B: EvaluationsOnDomain<F>,
}

// TODO for debugging: add test that checks result of arithmetize_matrix(M).
pub(crate) fn arithmetize_matrix<F: PrimeField>(
    matrix_name: &str,
    matrix: &mut Matrix<F>,
    interpolation_domain: &Box<dyn EvaluationDomain<F>>,
    output_domain: &Box<dyn EvaluationDomain<F>>,
    input_domain: &Box<dyn EvaluationDomain<F>>,
    expanded_domain: &Box<dyn EvaluationDomain<F>>,
) -> Result<MatrixArithmetization<F>, Error> {
    let matrix_time = start_timer!(|| "Computing row, col, and val LDEs");

    let elems: Vec<_> = output_domain.elements().collect();

    let mut row_vec = Vec::new();
    let mut col_vec = Vec::new();
    let mut val_vec = Vec::new();

    let eq_poly_vals_time = start_timer!(|| "Precomputing eq_poly_vals");
    let eq_poly_vals: BTreeMap<F, F> = output_domain
        .elements()
        .zip(output_domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs())
        .collect();
    end_timer!(eq_poly_vals_time);

    let lde_evals_time = start_timer!(|| "Computing row, col and val evals");
    let mut inverses = Vec::new();

    let mut count = 0;

    // Recall that we are computing the arithmetization of M^*,
    // where `M^*(i, j) := M(j, i) * u_H(j, j)`.
    for (r, row) in matrix.iter_mut().enumerate() {
        if !is_in_ascending_order(&row, |(_, a), (_, b)| a < b) {
            row.sort_by(|(_, a), (_, b)| a.cmp(b));
        };

        for &mut (val, i) in row {
            let row_val = elems[r];
            let col_val = elems[output_domain
                .reindex_by_subdomain(input_domain.size(), i)
                .map_err(|e| Error::Other(e.to_string()))?];

            // We are dealing with the transpose of M
            row_vec.push(col_val);
            col_vec.push(row_val);
            val_vec.push(val);
            inverses.push(eq_poly_vals[&col_val]);

            count += 1;
        }
    }
    algebra::fields::batch_inversion::<F>(&mut inverses);

    val_vec
        .par_iter_mut()
        .zip(inverses)
        .for_each(|(v, inv)| *v *= &inv);
    end_timer!(lde_evals_time);

    for _ in 0..(interpolation_domain.size() - count) {
        col_vec.push(elems[0]);
        row_vec.push(elems[0]);
        val_vec.push(F::zero());
    }
    let row_col_vec: Vec<_> = row_vec
        .iter()
        .zip(&col_vec)
        .map(|(row, col)| *row * col)
        .collect();

    let interpolate_time = start_timer!(|| "Interpolating on K and B");
    let row_evals_on_K =
        EvaluationsOnDomain::from_vec_and_domain(row_vec, interpolation_domain.clone());
    let col_evals_on_K =
        EvaluationsOnDomain::from_vec_and_domain(col_vec, interpolation_domain.clone());
    let val_evals_on_K =
        EvaluationsOnDomain::from_vec_and_domain(val_vec, interpolation_domain.clone());
    let row_col_evals_on_K =
        EvaluationsOnDomain::from_vec_and_domain(row_col_vec, interpolation_domain.clone());

    let row = row_evals_on_K.clone().interpolate();
    let col = col_evals_on_K.clone().interpolate();
    let val = val_evals_on_K.clone().interpolate();
    let row_col = row_col_evals_on_K.interpolate();

    let row_evals_on_B = EvaluationsOnDomain::from_vec_and_domain(
        expanded_domain.fft(&row),
        expanded_domain.clone(),
    );
    let col_evals_on_B = EvaluationsOnDomain::from_vec_and_domain(
        expanded_domain.fft(&col),
        expanded_domain.clone(),
    );
    let val_evals_on_B = EvaluationsOnDomain::from_vec_and_domain(
        expanded_domain.fft(&val),
        expanded_domain.clone(),
    );
    let row_col_evals_on_B = EvaluationsOnDomain::from_vec_and_domain(
        expanded_domain.fft(&row_col),
        expanded_domain.clone(),
    );
    end_timer!(interpolate_time);

    end_timer!(matrix_time);
    let evals_on_K = MatrixEvals {
        row: row_evals_on_K,
        col: col_evals_on_K,
        val: val_evals_on_K,
    };
    let evals_on_B = MatrixEvals {
        row: row_evals_on_B,
        col: col_evals_on_B,
        val: val_evals_on_B,
    };

    let m_name = matrix_name.to_string();
    Ok(MatrixArithmetization {
        row: LabeledPolynomial::new(m_name.clone() + "_row", row, None, None),
        col: LabeledPolynomial::new(m_name.clone() + "_col", col, None, None),
        val: LabeledPolynomial::new(m_name.clone() + "_val", val, None, None),
        row_col: LabeledPolynomial::new(m_name + "_row_col", row_col, None, None),
        evals_on_K,
        evals_on_B,
        row_col_evals_on_B,
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
