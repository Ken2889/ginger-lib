#![allow(non_snake_case)]

use crate::ahp::{
    constraint_systems::{
        arithmetize_matrix, make_matrices_square, num_non_zero, pad_input, process_matrices,
        MatrixArithmetization,
    },
    AHPForR1CS, Error,
};
use crate::Vec;
use algebra::get_best_evaluation_domain;
use algebra::{serialize::*, PrimeField, SemanticallyValid, ToBytes};
use derivative::Derivative;
use poly_commit::LabeledPolynomial;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, SynthesisMode};

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
    /// The maximum number of non-zero entries in any constraint matrix.
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
    /// the AHP.
    pub fn max_degree(&self, zk: bool) -> Result<usize, Error> {
        AHPForR1CS::<F>::max_degree(
            self.num_constraints,
            self.num_witness + self.num_inputs,
            self.num_non_zero,
            zk,
        )
    }
}

/// Represents a matrix.
pub type Matrix<F> = Vec<Vec<(F, usize)>>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
/// The indexed version of the constraint system.
/// This struct contains three kinds of objects:
/// 1) `index_info` is information about the index, such as the size of the
///     public input
/// 2) `{a,b,c}` are the matrices defining the R1CS instance
/// 3) `{a,b,c}_star_arith` are structs containing information about A^*, B^*, and C^*,
/// which are matrices defined as `M^*(i, j) = M(j, i) * u_H(j, j)`.
pub struct Index<F: PrimeField> {
    /// Information about the index.
    pub index_info: IndexInfo<F>,

    /// The A matrix for the R1CS instance
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance
    pub c: Matrix<F>,

    /// Arithmetization of the A* matrix.
    pub a_star_arith: MatrixArithmetization<F>,
    /// Arithmetization of the B* matrix.
    pub b_star_arith: MatrixArithmetization<F>,
    /// Arithmetization of the C* matrix.
    pub c_star_arith: MatrixArithmetization<F>,
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
            let d = get_best_evaluation_domain::<F>(3 * domain_k.size() - 3);
            if d.is_none() {
                return false;
            }
            d.unwrap()
        };

        let padded_dim = std::cmp::max(
            self.index_info.num_constraints,
            self.index_info.num_witness + self.index_info.num_inputs,
        );

        let check_matrix = &|m: &Matrix<F>, m_star_arith: &MatrixArithmetization<F>| -> bool {
            // Check number of rows is the correct one
            if m.len() != padded_dim {
                return false;
            };

            // Check each element being valid and the index of each variable being below the padded dim
            // (we use a sparse matrix representation, so that's the only way for us to check the square
            // condition on the columns)
            for row in m.iter() {
                for (val, idx) in row.iter() {
                    if !(val.is_valid() && *idx < padded_dim) {
                        return false;
                    }
                }
            }

            // Check indexer polys are not hiding and don't have any degree bound
            !m_star_arith.row.is_hiding() && m_star_arith.row.degree_bound().is_none() &&
                !m_star_arith.col.is_hiding() && m_star_arith.col.degree_bound().is_none() &&
                !m_star_arith.val.is_hiding() && m_star_arith.val.degree_bound().is_none() &&
                !m_star_arith.row_col.is_hiding() && m_star_arith.row_col.degree_bound().is_none() &&

            // Check correct number of evaluations on domain K
            m_star_arith.evals_on_K.row.evals.len() == domain_k.size() && &m_star_arith.evals_on_K.row.domain == &domain_k &&
                m_star_arith.evals_on_K.col.evals.len() == domain_k.size() && &m_star_arith.evals_on_K.col.domain == &domain_k &&
                m_star_arith.evals_on_K.val.evals.len() == domain_k.size() && &m_star_arith.evals_on_K.val.domain == &domain_k &&

            // Check correct number of evaluations on domain B
            m_star_arith.evals_on_B.row.evals.len() == domain_b.size() && &m_star_arith.evals_on_B.row.domain == &domain_b &&
                m_star_arith.evals_on_B.col.evals.len() == domain_b.size() && &m_star_arith.evals_on_B.col.domain == &domain_b &&
                m_star_arith.evals_on_B.val.evals.len() == domain_b.size() && &m_star_arith.evals_on_B.val.domain == &domain_b &&
                m_star_arith.row_col_evals_on_B.evals.len()  == domain_b.size() && &m_star_arith.row_col_evals_on_B.domain == &domain_b
        };

        check_matrix(&self.a, &self.a_star_arith)
            && check_matrix(&self.b, &self.b_star_arith)
            && check_matrix(&self.c, &self.c_star_arith)
    }
}

impl<F: PrimeField> Index<F> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self, zk: bool) -> Result<usize, Error> {
        self.index_info.max_degree(zk)
    }

    /// Iterate over the indexed polynomials.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![
            &self.a_star_arith.row,
            &self.a_star_arith.col,
            &self.a_star_arith.val,
            &self.a_star_arith.row_col,
            &self.b_star_arith.row,
            &self.b_star_arith.col,
            &self.b_star_arith.val,
            &self.b_star_arith.row_col,
            &self.c_star_arith.row,
            &self.c_star_arith.col,
            &self.c_star_arith.val,
            &self.c_star_arith.row_col,
        ]
        .into_iter()
    }
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Generate the index for this constraint system.
    pub fn index<C: ConstraintSynthesizer<F>>(c: C) -> Result<Index<F>, Error> {
        let index_time = start_timer!(|| "AHP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let mut ics = ConstraintSystem::new(SynthesisMode::Setup);
        c.generate_constraints(&mut ics)?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        let num_inputs = ics.num_inputs;
        pad_input(&mut ics, num_inputs);
        make_matrices_square(&mut ics);
        end_timer!(padding_time);
        let matrix_processing_time = start_timer!(|| "Processing matrices");
        let (mut a, mut b, mut c) = process_matrices(&mut ics).expect("should not be `None`");
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

        let num_formatted_input_variables = ics.num_inputs;
        let num_witness_variables = ics.num_aux;
        let num_constraints = ics.num_constraints;
        let nnz = num_non_zero(&mut ics);

        if num_constraints != num_formatted_input_variables + num_witness_variables {
            eprintln!(
                "number of (formatted) input_variables: {}",
                num_formatted_input_variables
            );
            eprintln!("number of witness_variables: {}", num_witness_variables);
            eprintln!("number of num_constraints: {}", num_constraints);
            eprintln!("number of num_non_zero: {}", num_non_zero(&mut ics));
            return Err(Error::NonSquareMatrix);
        }

        if !Self::num_formatted_public_inputs_is_admissible(num_formatted_input_variables) {
            return Err(Error::InvalidPublicInputLength);
        }

        let index_info = IndexInfo {
            num_witness: num_witness_variables,
            num_inputs: num_formatted_input_variables,
            num_constraints,
            num_non_zero: nnz,

            f: PhantomData,
        };

        let domain_h = get_best_evaluation_domain::<F>(num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k =
            get_best_evaluation_domain::<F>(nnz).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let x_domain = get_best_evaluation_domain(num_formatted_input_variables)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let b_domain = get_best_evaluation_domain(3 * domain_k.size() - 3)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let a_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let a_star_arith =
            arithmetize_matrix("a", &mut a, &domain_k, &domain_h, &x_domain, &b_domain)?;
        end_timer!(a_arithmetization_time);

        let b_arithmetization_time = start_timer!(|| "Arithmetizing B");
        let b_star_arith =
            arithmetize_matrix("b", &mut b, &domain_k, &domain_h, &x_domain, &b_domain)?;
        end_timer!(b_arithmetization_time);

        let c_arithmetization_time = start_timer!(|| "Arithmetizing C");
        let c_star_arith =
            arithmetize_matrix("c", &mut c, &domain_k, &domain_h, &x_domain, &b_domain)?;
        end_timer!(c_arithmetization_time);

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
