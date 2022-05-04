#![allow(non_snake_case)]

use algebra::{get_best_evaluation_domain, serialize::*, DualCycle, EvaluationDomain, ToBytes};
use derivative::Derivative;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisMode};

use crate::darlin::t_dlog_acc_marlin::iop::IOP;
use crate::darlin::IPACurve;
use bench_utils::{add_to_trace, end_timer, start_timer};
use marlin::iop::indexer::{balance_matrices, num_non_zero, post_process_matrices};
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
pub struct IndexInfo<G1: IPACurve> {
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
}

impl<G1: IPACurve> IndexInfo<G1> {
    pub fn get_domain_h(&self) -> Option<Box<dyn EvaluationDomain<G1::ScalarField>>> {
        get_best_evaluation_domain(std::cmp::max(
            self.num_constraints,
            self.num_witness + self.num_inputs,
        ))
    }
}

impl<G1: IPACurve> ToBytes for IndexInfo<G1> {
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
pub struct Index<G1: IPACurve> {
    /// Information about the index.
    pub index_info: IndexInfo<G1>,

    /// The `A` matrix for the R1CS instance, in sparse representation.
    pub a: SparseMatrix<G1::ScalarField>,
    /// The `B` matrix for the R1CS instance, in sparse representation.
    pub b: SparseMatrix<G1::ScalarField>,
    /// The `C` matrix for the R1CS instance, in sparse representation
    pub c: SparseMatrix<G1::ScalarField>,
}

impl<G1, G2> IOP<G1, G2>
where
    G1: IPACurve,
    G2: IPACurve,
    G1: DualCycle<G2>,
{
    /// Generate the index for this constraint system, which essentially contains
    /// the indexer polynomials for the R1CS matrices.
    pub fn index<C: ConstraintSynthesizer<G1::ScalarField>>(c: C) -> Result<Index<G1>, Error> {
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
            g1: PhantomData,
        };

        let (domain_h, _, domain_x, _) = marlin::IOP::build_domains(
            index_info.num_witness,
            index_info.num_inputs,
            index_info.num_constraints,
            index_info.num_non_zero,
        )?;

        let (a, b, c) =
            post_process_matrices(&mut ics, &domain_h, &domain_x).expect("should not be `None`");

        end_timer!(index_time);
        Ok(Index {
            index_info,
            a,
            b,
            c,
        })
    }
}
