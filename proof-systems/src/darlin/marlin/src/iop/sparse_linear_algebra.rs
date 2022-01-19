// TODO: vector-matrix arithmetics should be ideally outsourced to a module of the
// `algebra` crate.
use algebra::Field;

/// Internal representation of a sparse matrix.
/// Each row is described by a vector of `(value, column_index)`- pairs.
pub type SparseMatrix<F> = Vec<Vec<(F, usize)>>;

/// Multiplication of a SparseMatrix by a vector
pub fn mat_vec_mul<F: Field>(matrix: &SparseMatrix<F>, v: &[F]) -> Vec<F> {
    let num_rows = matrix.len();
    let mut out = vec![F::zero(); num_rows];
    for (r, row) in matrix.iter().enumerate() {
        for (coeff, c) in row {
            out[r] += *coeff * v[*c];
        }
    }
    out
}
