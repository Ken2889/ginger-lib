// TODO: vector-matrix arithmetics should be ideally outsourced to a module of the
// `algebra` crate.
use algebra::Field;

/// Internal representation of a sparse matrix.
/// Each row is described by a vector of `(value, column_index)`- pairs.
pub type SparseMatrix<F> = Vec<Vec<(F, usize)>>;

/// Multiplication of a SparseMatrix by a vector.
/// This functions handles non-compatible  matrix-vector dimensions by (implicitly) padding the
/// vector by zeroes to match the number of columns of the matrix.
pub fn mat_vec_mul<F: Field>(matrix: &SparseMatrix<F>, v: &[F]) -> Vec<F> {
    let num_rows = matrix.len();
    let mut out = vec![F::zero(); num_rows];
    for (r, row) in matrix.iter().enumerate() {
        for (coeff, c) in row {
            let v_c = v.get(*c);
            if v_c.is_some() {
                out[r] += *coeff * v_c.unwrap();
            }
        }
    }
    out
}

#[cfg(test)]
pub(crate) mod test {
    // use crate::iop::sparse_linear_algebra::SparseMatrix;
    use crate::iop::sparse_linear_algebra::{mat_vec_mul, SparseMatrix};
    use algebra::fields::tweedle::fq::Fq as F;
    use algebra::{Field, UniformRand};
    use num_traits::Zero;
    use rand::distributions::{Bernoulli, Distribution, Uniform};
    use rand::{thread_rng, Rng, RngCore};

    pub(crate) struct DenseMatrix<F: Field> {
        pub(crate) val: Vec<F>,
        pub(crate) num_rows: usize,
        pub(crate) num_cols: usize,
    }

    impl<F: Field> DenseMatrix<F> {
        pub(crate) fn generate_random(
            num_rows: usize,
            num_cols: usize,
            fill_factor: f64,
            rng: &mut dyn RngCore,
        ) -> Self {
            let num_elems = num_rows * num_cols;
            let dist = Bernoulli::new(fill_factor).unwrap();
            let val: Vec<F> = (0..num_elems)
                .map(|_| match dist.sample(rng) {
                    true => F::rand(rng),
                    false => F::zero(),
                })
                .collect();

            Self {
                val,
                num_rows,
                num_cols,
            }
        }
        pub(crate) fn vec_mul(&self, vec: &[F]) -> Vec<F> {
            let mut res = Vec::new();
            for i in 0..self.num_rows {
                let mut acc = F::zero();
                for j in 0..self.num_cols {
                    acc += self.val[i * self.num_cols + j] * vec[j];
                }
                res.push(acc);
            }
            res
        }
        pub(crate) fn to_sparse(&self) -> SparseMatrix<F> {
            let mut res = Vec::new();
            for i in 0..self.num_rows {
                let mut acc = Vec::new();
                for j in 0..self.num_cols {
                    let val = self.val[i * self.num_cols + j];
                    if !val.is_zero() {
                        acc.push((val, j));
                    }
                }
                res.push(acc);
            }
            res
        }
    }

    pub(crate) fn generate_random_vector<F: Field>(len: usize, rng: &mut dyn RngCore) -> Vec<F> {
        let vec: Vec<F> = (0..len).map(|_| UniformRand::rand(rng)).collect();
        vec
    }

    #[test]
    fn mat_vec_mul_square() {
        let rng = &mut thread_rng();

        let num_rounds = 100;
        let size_dist = Uniform::from(1..100);
        let fill_factor_dist = Uniform::new(0.0, 1.0);

        for _ in 0..num_rounds {
            let num_rows = size_dist.sample(rng);
            let num_cols = num_rows;
            let fill_factor = fill_factor_dist.sample(rng);
            let dense_matrix =
                DenseMatrix::<F>::generate_random(num_rows, num_cols, fill_factor, rng);
            let sparse_matrix = dense_matrix.to_sparse();
            let vec = generate_random_vector(num_cols, rng);

            let dense_product = dense_matrix.vec_mul(&vec);
            let sparse_product = mat_vec_mul(&sparse_matrix, &vec);
            assert_eq!(dense_product, sparse_product);
        }
    }

    #[test]
    fn mat_vec_mul_tall() {
        let rng = &mut thread_rng();

        let num_rounds = 100;
        let num_rows_dist = Uniform::from(10..100);
        let num_cols_dist = Uniform::from(1..10);
        let fill_factor_dist = Uniform::new(0.0, 1.0);

        for _ in 0..num_rounds {
            let num_rows = num_rows_dist.sample(rng);
            let num_cols = num_cols_dist.sample(rng);
            let fill_factor = fill_factor_dist.sample(rng);
            let dense_matrix =
                DenseMatrix::<F>::generate_random(num_rows, num_cols, fill_factor, rng);
            let sparse_matrix = dense_matrix.to_sparse();
            let vec = generate_random_vector(num_cols, rng);

            let dense_product = dense_matrix.vec_mul(&vec);
            let sparse_product = mat_vec_mul(&sparse_matrix, &vec);
            assert_eq!(dense_product, sparse_product);
        }
    }

    #[test]
    fn mat_vec_mul_squat() {
        let rng = &mut thread_rng();

        let num_rounds = 100;
        let num_rows_dist = Uniform::from(1..10);
        let num_cols_dist = Uniform::from(10..100);
        let fill_factor_dist = Uniform::new(0.0, 1.0);

        for _ in 0..num_rounds {
            let num_rows = num_rows_dist.sample(rng);
            let num_cols = num_cols_dist.sample(rng);
            let fill_factor = fill_factor_dist.sample(rng);
            let dense_matrix =
                DenseMatrix::<F>::generate_random(num_rows, num_cols, fill_factor, rng);
            let sparse_matrix = dense_matrix.to_sparse();
            let vec = generate_random_vector(num_cols, rng);

            let dense_product = dense_matrix.vec_mul(&vec);
            let sparse_product = mat_vec_mul(&sparse_matrix, &vec);
            assert_eq!(dense_product, sparse_product);
        }
    }

    #[test]
    fn mat_vec_mul_shorter_vec() {
        let rng = &mut thread_rng();

        let num_rounds = 100;
        let matrix_size_dist = Uniform::from(1..100);
        let fill_factor_dist = Uniform::new(0.0, 1.0);

        for _ in 0..num_rounds {
            let num_rows = matrix_size_dist.sample(rng);
            let num_cols = matrix_size_dist.sample(rng);
            let fill_factor = fill_factor_dist.sample(rng);
            let vec_size = rng.gen_range(1..=num_cols);
            let dense_matrix =
                DenseMatrix::<F>::generate_random(num_rows, num_cols, fill_factor, rng);
            let sparse_matrix = dense_matrix.to_sparse();
            let mut vec = generate_random_vector(num_cols, rng);
            for i in vec[vec_size..].iter_mut() {
                *i = F::zero();
            }

            let dense_product = dense_matrix.vec_mul(&vec);
            let sparse_product = mat_vec_mul(&sparse_matrix, &vec[0..vec_size]);
            assert_eq!(dense_product, sparse_product);
        }
    }

    #[test]
    fn mat_vec_mul_longer_vec() {
        let rng = &mut thread_rng();

        let num_rounds = 100;
        let matrix_size_dist = Uniform::from(1..100);
        let fill_factor_dist = Uniform::new(0.0, 1.0);

        for _ in 0..num_rounds {
            let num_rows = matrix_size_dist.sample(rng);
            let num_cols = matrix_size_dist.sample(rng);
            let fill_factor = fill_factor_dist.sample(rng);
            let num_additional_vec_elems = matrix_size_dist.sample(rng);
            let dense_matrix =
                DenseMatrix::<F>::generate_random(num_rows, num_cols, fill_factor, rng);
            let sparse_matrix = dense_matrix.to_sparse();
            let vec = generate_random_vector(num_cols + num_additional_vec_elems, rng);

            let dense_product = dense_matrix.vec_mul(&vec[0..num_cols]);
            let sparse_product = mat_vec_mul(&sparse_matrix, &vec);
            assert_eq!(dense_product, sparse_product);
        }
    }

    #[test]
    fn mat_vec_mul_missing_rows() {
        let rng = &mut thread_rng();

        let num_rounds = 100;
        let matrix_size_dist = Uniform::from(1..100);
        let fill_factor_dist = Uniform::new(0.0, 1.0);
        let bernoulli_param_dist = Uniform::new(0.0, 1.0);

        for _ in 0..num_rounds {
            let num_rows = matrix_size_dist.sample(rng);
            let num_cols = matrix_size_dist.sample(rng);
            let fill_factor = fill_factor_dist.sample(rng);
            let mut dense_matrix =
                DenseMatrix::<F>::generate_random(num_rows, num_cols, fill_factor, rng);

            let bernoulli_param = bernoulli_param_dist.sample(rng);
            let missing_row_dist = Bernoulli::new(bernoulli_param).unwrap();
            for i in 0..num_rows {
                if missing_row_dist.sample(rng) {
                    for val in dense_matrix.val[i * num_cols..(i + 1) * num_cols].iter_mut() {
                        *val = F::zero();
                    }
                }
            }
            let sparse_matrix = dense_matrix.to_sparse();
            let vec = generate_random_vector(num_cols, rng);

            let dense_product = dense_matrix.vec_mul(&vec);
            let sparse_product = mat_vec_mul(&sparse_matrix, &vec);
            assert_eq!(dense_product, sparse_product);
        }
    }
}
