#![allow(non_snake_case)]

use crate::iop::*;
use crate::iop::{Error, IOP};
use crate::{ToString, Vec};
use algebra::{
    get_best_evaluation_domain, serialize::*, EvaluationDomain, Evaluations as EvaluationsOnDomain,
    PrimeField, SemanticallyValid,
};
use derivative::Derivative;
use poly_commit::LabeledPolynomial;
use r1cs_core::{
    ConstraintSynthesizer, ConstraintSystem, Index as VarIndex, SynthesisError, SynthesisMode,
};

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

impl<F: PrimeField> IndexInfo<F> {
    /// The maximum degree of polynomial required to represent this index in the
    /// the IOP.
    pub fn max_degree(&self, zk: bool) -> Result<usize, Error> {
        IOP::<F>::max_degree(
            self.num_constraints,
            self.num_witness + self.num_inputs,
            self.num_non_zero,
            zk,
        )
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
/// Besides auxiliary information on the index, contains the R1CS matrices `M=A,B,C` and their
/// arithmetization using the (normalized) Lagrange kernel.
pub struct Index<F: PrimeField> {
    /// Information about the index.
    pub index_info: IndexInfo<F>,

    /// The `A` matrix for the R1CS instance, in sparse representation.
    pub a: SparseMatrix<F>,
    /// The `B` matrix for the R1CS instance, in sparse representation.
    pub b: SparseMatrix<F>,
    /// The `C` matrix for the R1CS instance, in sparse representation
    pub c: SparseMatrix<F>,

    /// Arithmetization of the matrix`A`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, `row.col(X)`, and `val.row.col(X)` of it.
    pub a_arith: MatrixArithmetization<F>,
    /// Arithmetization of the matrix`B`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, `row.col(X)`, and `val.row.col(X)` of it.
    pub b_arith: MatrixArithmetization<F>,
    /// Arithmetization of the matrix`C`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, `row.col(X)`, and `val.row.col(X)` of it.
    pub c_arith: MatrixArithmetization<F>,

    #[cfg(feature = "circuit-friendly")]
    /// The vanishing polynomials over domains H, K, and X.
    pub vanishing_polys: Vec<LabeledPolynomial<F>>,
}

impl<F: PrimeField> SemanticallyValid for Index<F> {
    fn is_valid(&self) -> bool {
        let domain_k = {
            let d = get_best_evaluation_domain::<F>(self.index_info.num_non_zero);
            if d.is_none() {
                return false;
            }
            d.unwrap()
        };

        let domain_b = {
            let d = get_best_evaluation_domain::<F>(4 * (domain_k.size() - 1));
            if d.is_none() {
                return false;
            }
            d.unwrap()
        };

        let check_matrix = &|m_arith: &MatrixArithmetization<F>| -> bool {
            // Check indexer polys are not hiding and don't have any degree bound
            !m_arith.row.is_hiding()
                && !m_arith.col.is_hiding()
                && !m_arith.row_col.is_hiding()
                && !m_arith.val_row_col.is_hiding()

            // Check correct number of evaluations on domain B
            && m_arith.evals_on_domain_b.row.evals.len() == domain_b.size()
                && &m_arith.evals_on_domain_b.row.domain == &domain_b
                && m_arith.evals_on_domain_b.col.evals.len() == domain_b.size()
                && &m_arith.evals_on_domain_b.col.domain == &domain_b
                && m_arith.evals_on_domain_b.row_col.evals.len() == domain_b.size()
                && &m_arith.evals_on_domain_b.row_col.domain == &domain_b
                && m_arith.evals_on_domain_b.val_row_col.evals.len() == domain_b.size()
                && &m_arith.evals_on_domain_b.val_row_col.domain == &domain_b
        };

        check_matrix(&self.a_arith) && check_matrix(&self.b_arith) && check_matrix(&self.c_arith)
    }
}

impl<F: PrimeField> Index<F> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self, zk: bool) -> Result<usize, Error> {
        self.index_info.max_degree(zk)
    }

    /// Iterate over the indexed polynomials.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        let result = vec![
            &self.a_arith.row,
            &self.a_arith.col,
            &self.a_arith.row_col,
            &self.a_arith.val_row_col,
            &self.b_arith.row,
            &self.b_arith.col,
            &self.b_arith.row_col,
            &self.b_arith.val_row_col,
            &self.c_arith.row,
            &self.c_arith.col,
            &self.c_arith.row_col,
            &self.c_arith.val_row_col,
        ]
        .into_iter();

        #[cfg(feature = "circuit-friendly")]
        let result = result.chain(self.vanishing_polys.iter());

        result
    }
}

impl<F: PrimeField> IOP<F> {
    /// Build the four domains used in the protocol.
    /// `num_aux` is the number of private witnesses
    /// `num_inputs` is the number of public inputs (including the one for the constants)
    /// `num_non_zero` is the max number of non-zero values in any of the matrices A, B, and C
    pub fn build_domains(
        num_aux: usize,
        num_inputs: usize,
        num_constraints: usize,
        num_non_zero: usize,
    ) -> Result<
        (
            Box<dyn EvaluationDomain<F>>,
            Box<dyn EvaluationDomain<F>>,
            Box<dyn EvaluationDomain<F>>,
            Box<dyn EvaluationDomain<F>>,
        ),
        Error,
    > {
        let num_formatted_variables = num_aux + num_inputs;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h = get_best_evaluation_domain::<F>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = get_best_evaluation_domain::<F>(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        // FFT domain for the public inputs, typically small
        let domain_x = get_best_evaluation_domain(num_inputs)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        // helper domain for the precomputations of the inner sumcheck
        let domain_b = get_best_evaluation_domain(4 * (domain_k.size() - 1))
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        Ok((domain_h, domain_k, domain_x, domain_b))
    }
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
        balance_matrices(&mut ics.at, &mut ics.bt);
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
        let (domain_h, domain_k, domain_x, domain_b) = Self::build_domains(
            index_info.num_witness,
            index_info.num_inputs,
            index_info.num_constraints,
            index_info.num_non_zero,
        )?;

        let (mut a, mut b, mut c) =
            post_process_matrices(&mut ics, &domain_h, &domain_x).expect("should not be `None`");

        let a_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let a_arith = arithmetize_matrix("a", &mut a, &domain_k, &domain_h, &domain_b)?;
        end_timer!(a_arithmetization_time);

        let b_arithmetization_time = start_timer!(|| "Arithmetizing B");
        let b_arith = arithmetize_matrix("b", &mut b, &domain_k, &domain_h, &domain_b)?;
        end_timer!(b_arithmetization_time);

        let c_arithmetization_time = start_timer!(|| "Arithmetizing C");
        let c_arith = arithmetize_matrix("c", &mut c, &domain_k, &domain_h, &domain_b)?;
        end_timer!(c_arithmetization_time);

        #[cfg(feature = "circuit-friendly")]
        let vanishing_polys = {
            let vanishing_polys_time =
                start_timer!(|| "Commit to vanishing polys on domains H, K, and X");
            let vanishing_polys = vec![
                LabeledPolynomial::new("v_h".into(), domain_h.vanishing_polynomial().into(), false),
                LabeledPolynomial::new("v_k".into(), domain_k.vanishing_polynomial().into(), false),
                LabeledPolynomial::new("v_x".into(), domain_x.vanishing_polynomial().into(), false),
            ];
            end_timer!(vanishing_polys_time);
            vanishing_polys
        };

        end_timer!(index_time);
        Ok(Index {
            index_info,
            a,
            b,
            c,
            a_arith,
            b_arith,
            c_arith,
            #[cfg(feature = "circuit-friendly")]
            vanishing_polys,
        })
    }
}

/***************************************************************************

    Indexer related structs and functions around matrix arithmetization

****************************************************************************/

/// Contains information about the arithmetization of a sparse matrix `M`,
/// as obtained by the lincheck to sumcheck reduction.
/// The arithmetization is with respect to the Lagrange kernel `L_H(X,Y)`, i.e.
///     `M(X,Y) = Sum_{z in K} val(z) * L_H(X,row(z)) * L_H(Y,col(z))`
/// over an *indexer domain* `K`, large enough to index the non-zero entries in
/// `M`.
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct MatrixArithmetization<F: PrimeField> {
    /// The polynomial for the row indices of `R_M`, in reduced form.
    pub row: LabeledPolynomial<F>,
    /// The polynomial for the column indices of `R_M`, in reduced form.
    pub col: LabeledPolynomial<F>,
    /// The reduced form of `row(X)*col(X)`.
    pub row_col: LabeledPolynomial<F>,
    /// The reduced form of `val(X)*row(X)*col(X)`.
    pub val_row_col: LabeledPolynomial<F>,

    //
    // Inner sumcheck precomputations:
    //
    /// Evaluation of indexer polynomials over the product domain `domain_b` (of size `4*|K|`)
    /// used in the prover computation for the inner sumcheck.
    pub evals_on_domain_b: MatrixEvals<F>,
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
/// Evaluations of indexer polynomials over a domain.
pub struct MatrixEvals<F: PrimeField> {
    /// Evaluation of `self.row`.
    pub row: EvaluationsOnDomain<F>,

    /// Evaluation of `self.col`.
    pub col: EvaluationsOnDomain<F>,

    /// Evaluation of `self.row_col`.
    pub row_col: EvaluationsOnDomain<F>,

    /// Evaluation of `self.val_row_col`.
    pub val_row_col: EvaluationsOnDomain<F>,
}

/// Given a sparse matrix `M`, computes the polynomial representations `row(X)`, `col(X)`,
/// `row.col(X)`, and `val.row.col(X)` of `M` such that
///   M(X,Y) = sum_{w in K} val(w) * L_H(X,row(w)) * L_H(Y,col(w))
/// where `K` is a domain large enough to index the non-zero entries of the matrix.
/// In order to ease prover computations we provide `val.row.col(X)` instead of `val(X)`.
/// For the same reason we also provide the polynomial `row.col(X)`.
pub(crate) fn arithmetize_matrix<F: PrimeField>(
    matrix_name: &str,
    // The R1CS matrix.
    matrix: &mut SparseMatrix<F>,
    // The indexer domain `K`.
    domain_k: &Box<dyn EvaluationDomain<F>>,
    // The domain `H` for the Lagrange representation of `M` .
    domain_h: &Box<dyn EvaluationDomain<F>>,
    // An extension of the indexer domain `K`, at least 4 times larger.
    domain_b: &Box<dyn EvaluationDomain<F>>,
) -> Result<MatrixArithmetization<F>, Error> {
    let matrix_time = start_timer!(|| format!("Arithemtizing matrix {}", matrix_name));

    let elems: Vec<_> = domain_h.elements().collect();

    let mut row_vec = Vec::with_capacity(domain_k.size());
    let mut col_vec = Vec::with_capacity(domain_k.size());
    let mut val_vec = Vec::with_capacity(domain_k.size());

    let lde_evals_time = start_timer!(|| "Computing row, col, row.col and val.row.col evals");

    for (r, row) in matrix.into_iter().enumerate() {
        if !is_in_ascending_order(&row, |(_, a), (_, b)| a < b) {
            row.sort_by(|(_, a), (_, b)| a.cmp(b));
        };

        for &mut (val, c) in row {
            row_vec.push(elems[r]);
            col_vec.push(elems[c]);
            val_vec.push(val);
        }
    }

    // pad to len equal to domain_k.size()
    row_vec.resize(domain_k.size(), elems[0]);
    col_vec.resize(domain_k.size(), elems[0]);
    val_vec.resize(domain_k.size(), F::zero());

    let (row_col_vec, val_row_col_vec): (Vec<_>, Vec<_>) = row_vec
        .par_iter()
        .zip(&col_vec)
        .zip(&val_vec)
        .map(|((row, col), val)| {
            let row_col = *row * col;
            (row_col, row_col * val)
        })
        .collect();

    end_timer!(lde_evals_time);

    let interpolate_time = start_timer!(|| "Interpolating on K and B");
    let row_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(row_vec, domain_k.clone());
    let col_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(col_vec, domain_k.clone());
    let row_col_evals_on_K =
        EvaluationsOnDomain::from_vec_and_domain(row_col_vec, domain_k.clone());
    let val_row_col_evals_on_K =
        EvaluationsOnDomain::from_vec_and_domain(val_row_col_vec, domain_k.clone());

    let row = row_evals_on_K.clone().interpolate();
    let col = col_evals_on_K.clone().interpolate();
    let row_col = row_col_evals_on_K.interpolate();
    let val_row_col = val_row_col_evals_on_K.interpolate();

    let evals_on_domain_b = {
        let row = EvaluationsOnDomain::from_vec_and_domain(domain_b.fft(&row), domain_b.clone());
        let col = EvaluationsOnDomain::from_vec_and_domain(domain_b.fft(&col), domain_b.clone());
        let row_col =
            EvaluationsOnDomain::from_vec_and_domain(domain_b.fft(&row_col), domain_b.clone());
        let val_row_col =
            EvaluationsOnDomain::from_vec_and_domain(domain_b.fft(&val_row_col), domain_b.clone());
        MatrixEvals {
            row,
            col,
            row_col,
            val_row_col,
        }
    };
    end_timer!(interpolate_time);

    end_timer!(matrix_time);

    let m_name = matrix_name.to_string();
    Ok(MatrixArithmetization {
        row: LabeledPolynomial::new(m_name.clone() + "_row", row, false),
        col: LabeledPolynomial::new(m_name.clone() + "_col", col, false),
        row_col: LabeledPolynomial::new(m_name.clone() + "_row_col", row_col, false),
        val_row_col: LabeledPolynomial::new(m_name.clone() + "_val_row_col", val_row_col, false),
        evals_on_domain_b,
    })
}

/// Checks that the slice `x_s` is ordered according to the criterion defined by `is_less_than`.
pub fn is_in_ascending_order<T: Ord>(x_s: &[T], is_less_than: impl Fn(&T, &T) -> bool) -> bool {
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
/// The columns of the matrix are re-arranged to be coherent with the treatment of input variables
/// as a subdomain of the full variable vector.
fn to_matrix_helper<F: PrimeField>(
    matrix: &[Vec<(F, VarIndex)>],
    domain_h: &Box<dyn EvaluationDomain<F>>,
    domain_x: &Box<dyn EvaluationDomain<F>>,
) -> SparseMatrix<F> {
    let mut new_matrix = Vec::with_capacity(matrix.len());
    let domain_x_size = domain_x.size();
    for row in matrix {
        let mut new_row = Vec::with_capacity(row.len());
        for (fe, column) in row {
            let column = match column {
                VarIndex::Input(i) => *i,
                VarIndex::Aux(i) => domain_x_size + i,
            };
            let index = domain_h
                .reindex_by_subdomain(domain_x_size, column)
                .unwrap();
            new_row.push((*fe, index))
        }
        new_matrix.push(new_row)
    }
    new_matrix
}

/// A simple function that balances the non-zero entries between A and B.
// TODO: write a test to check that `balance_matrices` improves the balancing of the matrices
// A and B by distributing the non-zero elements (more or less) evenly between the two.
pub fn balance_matrices<F: Field>(
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

/// Convert the A, B, and C matrices for the R1CS into the SparseMatrix format representation used
/// inside the proving system.
pub fn post_process_matrices<F: PrimeField>(
    cs: &mut ConstraintSystem<F>,
    domain_h: &Box<dyn EvaluationDomain<F>>,
    domain_x: &Box<dyn EvaluationDomain<F>>,
) -> Option<(SparseMatrix<F>, SparseMatrix<F>, SparseMatrix<F>)> {
    let a = to_matrix_helper(&cs.at, domain_h, domain_x);
    let b = to_matrix_helper(&cs.bt, domain_h, domain_x);
    let c = to_matrix_helper(&cs.ct, domain_h, domain_x);
    Some((a, b, c))
}

/// Return the number of non-zero elements of the R1CS matrices, that is the maximum number of non-
/// zero elements among matrices A, B, and C.
pub fn num_non_zero<F: Field>(cs: &mut ConstraintSystem<F>) -> usize {
    let a_non_zeros = cs.at.iter().map(|row| row.len()).sum();
    let b_non_zeros = cs.bt.iter().map(|row| row.len()).sum();
    let c_non_zeros = cs.ct.iter().map(|row| row.len()).sum();

    let max = *[a_non_zeros, b_non_zeros, c_non_zeros]
        .iter()
        .max()
        .expect("iterator is not empty");
    max
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::iop::sparse_linear_algebra::test::DenseMatrix;
    use crate::IOP;
    use algebra::fields::tweedle::fq::Fq as F;
    use algebra::UniformRand;
    use num_traits::{One, Zero};
    use rand::distributions::{Distribution, Uniform};
    use rand::{thread_rng, RngCore};

    fn build_random_matrix(
        num_inputs: usize,
        num_aux: usize,
        num_constraints: usize,
        fill_factor: f64,
        rng: &mut dyn RngCore,
    ) -> SparseMatrix<F> {
        let num_padded_inputs = get_best_evaluation_domain::<F>(num_inputs).unwrap().size();
        let mut matrix = DenseMatrix::<F>::generate_random(
            num_constraints,
            num_inputs + num_aux,
            fill_factor,
            rng,
        );
        for i in 0..matrix.num_rows {
            for j in 0..matrix.num_cols {
                if j >= num_inputs && j < num_padded_inputs {
                    matrix.val[i * matrix.num_cols + j] = F::zero();
                }
            }
        }
        matrix.to_sparse()
    }

    #[test]
    fn matrix_arithmetization() {
        let num_rounds = 100;

        let num_inputs_dist = Uniform::from(1..100);
        let num_aux_dist = Uniform::from(1..100);
        let num_constraints_dist = Uniform::from(1..200);
        let fill_factor_dist = Uniform::new(0.0, 1.0);

        let rng = &mut thread_rng();

        for _ in 0..num_rounds {
            let num_inputs = num_inputs_dist.sample(rng);
            let num_aux = num_aux_dist.sample(rng);
            let num_constraints = num_constraints_dist.sample(rng);
            let fill_factor = fill_factor_dist.sample(rng);

            let mut matrix =
                build_random_matrix(num_inputs, num_aux, num_constraints, fill_factor, rng);
            let num_non_zero = matrix.iter().map(|row| row.len()).sum();
            let (domain_h, domain_k, _domain_x, domain_b) =
                IOP::build_domains(num_aux, num_inputs, num_constraints, num_non_zero).unwrap();

            let arithmetization =
                arithmetize_matrix("m", &mut matrix, &domain_k, &domain_h, &domain_b).unwrap();

            // Random points for checking that dense and sparse representations of the matrix coincide
            let x = loop {
                let x = F::rand(rng);
                // check that x does not belong to domain_k
                if !domain_k.evaluate_vanishing_polynomial(x).is_zero() {
                    break x;
                }
            };
            let y = loop {
                let y = F::rand(rng);
                // check that y does not belong to domain_k
                if !domain_k.evaluate_vanishing_polynomial(y).is_zero() {
                    break y;
                }
            };

            // Evaluate M(x,y) using dense representation
            //   M(X,Y) = \sum_{i,j = 1...n} M_{i,j} * L(X, z_i) * L(Y, z_j)
            // where
            //   n is the size of the Lagrange domain H
            //   z_i for i = 1...n are the roots of unity associated to H
            //   L(.,.) is the bivariate Lagrange kernel
            let lagrange_h_x = domain_h.domain_eval_lagrange_kernel(x).unwrap();
            let lagrange_h_y = domain_h.domain_eval_lagrange_kernel(y).unwrap();
            let mut result_dense = F::zero();

            for (i, row) in matrix.iter().enumerate() {
                for &(val, j) in row {
                    result_dense += val * lagrange_h_x[i] * lagrange_h_y[j];
                }
            }

            // Evaluate M(x,y) using sparse representation.
            //   M(X,Y) = (X^n - 1)*(Y^n - 1)/n^2
            //            * \sum_{w \in K} val.row.col(w) / ((X - row(w))*(Y - col(w))) mod (X^m - 1)
            // where
            //   n is the size of the Lagrange domain H
            //   m is the size of the domain K
            let val_row_col_on_k = arithmetization
                .val_row_col
                .evaluate_over_domain_by_ref(domain_k.clone());
            let row_on_k = arithmetization
                .row
                .evaluate_over_domain_by_ref(domain_k.clone());
            let col_on_k = arithmetization.col.evaluate_over_domain_by_ref(domain_k);
            let scaling_factor = (x.pow(&[domain_h.size() as u64]) - F::one())
                * (y.pow(&[domain_h.size() as u64]) - F::one())
                * domain_h.size_inv()
                * domain_h.size_inv();
            let sparse_repr: F = row_on_k
                .evals
                .iter()
                .zip(col_on_k.evals.iter())
                .zip(val_row_col_on_k.evals.iter())
                .map(|((r, c), vrc)| *vrc / ((x - r) * (y - c)))
                .sum();
            let result_sparse = scaling_factor * sparse_repr;

            assert_eq!(result_dense, result_sparse);
        }
    }

    #[test]
    // - Matrix A: exactly 2 non-zero elements in each constraint
    // - Matrix B: exactly 1 non-zero element in each constraint
    // - Even number of constraints
    // In this situation the balancer should perfectly balance the matrices.
    fn matrix_balancer_even() {
        let num_constraints = 100;
        let mut a = vec![vec![(F::one(), VarIndex::Aux(0)); 2]; num_constraints];
        let mut b = vec![vec![(F::one(), VarIndex::Aux(0)); 1]; num_constraints];
        balance_matrices(&mut a, &mut b);
        let a_weight: usize = a.iter().map(|row| row.len()).sum();
        let b_weight: usize = b.iter().map(|row| row.len()).sum();
        assert_eq!(a_weight, b_weight);
    }
    #[test]
    // - Matrix A: exactly 2 non-zero elements in each constraint
    // - Matrix B: exactly 1 non-zero element in each constraint
    // - Odd number of constraints
    // In this situation the difference in the number of non-zero elements of A and B after
    // balancing should be equal to 1.
    fn matrix_balancer_odd() {
        let num_constraints = 101;
        let mut a = vec![vec![(F::one(), VarIndex::Aux(0)); 2]; num_constraints];
        let mut b = vec![vec![(F::one(), VarIndex::Aux(0)); 1]; num_constraints];
        balance_matrices(&mut a, &mut b);
        let a_weight: usize = a.iter().map(|row| row.len()).sum();
        let b_weight: usize = b.iter().map(|row| row.len()).sum();
        assert_eq!((a_weight as i64 - b_weight as i64).abs(), 1);
    }

    #[test]
    // Balancer should behave symmetrically with respect to its two arguments.
    fn matrix_balancer_symmetry() {
        let num_constraints = 10;
        let num_elements = Uniform::from(0..100);
        let rng = &mut thread_rng();
        let a: Vec<_> = (0..num_constraints)
            .into_iter()
            .map(|_| {
                let n = num_elements.sample(rng);
                vec![(F::one(), VarIndex::Aux(0)); n]
            })
            .collect();
        let b: Vec<_> = (0..num_constraints)
            .into_iter()
            .map(|_| {
                let n = num_elements.sample(rng);
                vec![(F::one(), VarIndex::Aux(0)); n]
            })
            .collect();

        let mut a1 = a.clone();
        let mut b1 = b.clone();
        balance_matrices(&mut a1, &mut b1);

        let mut a2 = a.clone();
        let mut b2 = b.clone();
        balance_matrices(&mut b2, &mut a2);

        assert_eq!(a1, a2);
        assert_eq!(b1, b2);
    }
}
