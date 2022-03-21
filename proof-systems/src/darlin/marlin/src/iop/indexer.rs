#![allow(non_snake_case)]

use crate::iop::*;
use crate::iop::{Error, IOP};
use crate::{ToString, Vec};
use algebra::{
    get_best_evaluation_domain, serialize::*, EvaluationDomain, Evaluations as EvaluationsOnDomain,
    PrimeField, SemanticallyValid, ToBytes,
};
use derivative::Derivative;
use poly_commit::LabeledPolynomial;
use r1cs_core::{
    ConstraintSynthesizer, ConstraintSystem, Index as VarIndex, SynthesisError, SynthesisMode,
};
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
    pub a: Vec<Vec<(F, VarIndex)>>,
    /// The `B` matrix for the R1CS instance, in sparse representation.
    pub b: Vec<Vec<(F, VarIndex)>>,
    /// The `C` matrix for the R1CS instance, in sparse representation
    pub c: Vec<Vec<(F, VarIndex)>>,

    /// Arithmetization of the matrix`A`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, `row.col(X)`, and `val.row.col(X)` of it.
    pub a_arith: MatrixArithmetization<F>,
    /// Arithmetization of the matrix`B`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, `row.col(X)`, and `val.row.col(X)` of it.
    pub b_arith: MatrixArithmetization<F>,
    /// Arithmetization of the matrix`C`, which essentially contains
    /// the indexer polynomials `row(X)`, `col(X)`, `row.col(X)`, and `val.row.col(X)` of it.
    pub c_arith: MatrixArithmetization<F>,
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
        vec![
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
        .into_iter()
    }
}

impl<F: PrimeField> IOP<F> {
    /// Build the four domains used in the protocol.
    /// `num_aux` is the number of private witnesses
    /// `num_inputs` is the number of public inputs (including the one for the constants)
    /// `num_non_zero` is the max number of non-zero values in any of the matrices A, B, and C
    pub(crate) fn build_domains(
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
        ics.balance_matrices();
        let num_non_zero = ics.num_non_zero();
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
        add_to_trace!(|| "number of num_non_zero", || format!("{}", num_non_zero));
        end_timer!(matrix_processing_time);

        let index_info = IndexInfo {
            num_witness: ics.num_aux,
            num_inputs: ics.num_inputs,
            num_constraints: ics.num_constraints,
            num_non_zero: num_non_zero,

            f: PhantomData,
        };
        let (domain_h, domain_k, domain_x, domain_b) = Self::build_domains(
            index_info.num_witness,
            index_info.num_inputs,
            index_info.num_constraints,
            index_info.num_non_zero,
        )?;

        let a_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let a_arith =
            arithmetize_matrix("a", &mut ics.at, &domain_x, &domain_k, &domain_h, &domain_b)?;
        end_timer!(a_arithmetization_time);

        let b_arithmetization_time = start_timer!(|| "Arithmetizing B");
        let b_arith =
            arithmetize_matrix("b", &mut ics.bt, &domain_x, &domain_k, &domain_h, &domain_b)?;
        end_timer!(b_arithmetization_time);

        let c_arithmetization_time = start_timer!(|| "Arithmetizing C");
        let c_arith =
            arithmetize_matrix("c", &mut ics.ct, &domain_x, &domain_k, &domain_h, &domain_b)?;
        end_timer!(c_arithmetization_time);

        end_timer!(index_time);
        Ok(Index {
            index_info,
            a: ics.at,
            b: ics.bt,
            c: ics.ct,
            a_arith,
            b_arith,
            c_arith,
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
    /// The size of the domain H.
    pub size_of_H: usize,
    /// The size of the domain K.
    pub size_of_K: usize,

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
    matrix: &mut Vec<Vec<(F, VarIndex)>>,
    // The public input domain `X`.
    domain_x: &Box<dyn EvaluationDomain<F>>,
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

        for &mut (val, c_varindex) in row {
            row_vec.push(elems[r]);
            col_vec.push(elems[varindex_to_linear_index(c_varindex, domain_h, domain_x)?]);
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
        size_of_H: domain_h.size(),
        size_of_K: domain_k.size(),
        evals_on_domain_b,
    })
}

/// Convert the column index from a `VarIndex` as used inside `ConstraintSystem` to a linear
/// index, with columns related to public inputs numbered accordingly to the treatment
/// of `domain_x` as a subdomain of `domain_h`.
pub(crate) fn varindex_to_linear_index<F: PrimeField>(
    var_index: VarIndex,
    domain_h: &Box<dyn EvaluationDomain<F>>,
    domain_x: &Box<dyn EvaluationDomain<F>>,
) -> Result<usize, Error> {
    let domain_x_size = domain_x.size();
    let idx = match var_index {
        VarIndex::Input(i) => i,
        VarIndex::Aux(i) => domain_x_size + i,
    };
    domain_h
        .reindex_by_subdomain(domain_x_size, idx)
        .map_err(|e| Error::Other(format!("{}", e)))
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
