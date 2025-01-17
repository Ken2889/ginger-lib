//! Core interface for working with Rank-1 Constraint Systems (R1CS).

#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public, variant_size_differences)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_imports, unused_mut, missing_docs)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]
#![allow(
    clippy::upper_case_acronyms,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::try_err,
    clippy::map_collect_result_unit,
    clippy::not_unsafe_ptr_arg_deref,
    clippy::suspicious_op_assign_impl,
    clippy::suspicious_arithmetic_impl,
    clippy::assertions_on_constants
)]

mod constraint_system;
mod error;
mod impl_constraint_var;
mod impl_lc;

pub use algebra::ToConstraintField;
pub use constraint_system::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger,
    Namespace, SynthesisMode,
};
pub use error::SynthesisError;

use algebra::Field;
use smallvec::SmallVec as StackVec;
use std::cmp::Ordering;

type SmallVec<F> = StackVec<[(Variable, F); 16]>;

/// Represents a variable in a constraint system.
#[derive(PartialOrd, Ord, PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct Variable(Index);

impl Variable {
    /// This constructs a variable with an arbitrary index.
    /// Circuit implementations are not recommended to use this.
    pub fn new_unchecked(idx: Index) -> Variable {
        Variable(idx)
    }

    /// This returns the index underlying the variable.
    /// Circuit implementations are not recommended to use this.
    pub fn get_unchecked(&self) -> Index {
        self.0
    }
}

/// Represents the index of either an input variable or auxiliary variable.
#[derive(Copy, Clone, PartialEq, Debug, Eq, Hash)]
pub enum Index {
    /// Index of an input variable.
    Input(usize),
    /// Index of an auxiliary (or private) variable.
    Aux(usize),
}

impl PartialOrd for Index {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Index {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Index::Input(ref idx1), Index::Input(ref idx2))
            | (Index::Aux(ref idx1), Index::Aux(ref idx2)) => idx1.cmp(idx2),
            (Index::Input(_), Index::Aux(_)) => Ordering::Less,
            (Index::Aux(_), Index::Input(_)) => Ordering::Greater,
        }
    }
}

/// This represents a linear combination of some variables, with coefficients
/// in the field `F`.
/// The `(coeff, var)` pairs in a `LinearCombination` are kept sorted according
/// to the index of the variable in its constraint system.
#[derive(Debug, Clone, Hash)]
pub struct LinearCombination<F: Field>(pub SmallVec<F>);

/// Either a `Variable` or a `LinearCombination`.
#[derive(Clone, Debug, Hash)]
pub enum ConstraintVar<F: Field> {
    /// A wrapper around a `LinearCombination`.
    LC(LinearCombination<F>),
    /// A wrapper around a `Variable`.
    Var(Variable),
}

/// Debug a circuit by looking for unsatisfied constraints.
/// If the circuit is satisfied, return `Ok(None)`.
/// If there are unsatisfied constraints, return `Ok(Some(name))`,
/// where `name` is the name of the first unsatisfied constraint.
pub fn debug_circuit<F: Field, C: ConstraintSynthesizer<F>>(
    circuit: C,
) -> Result<Option<String>, SynthesisError> {
    let mut cs = ConstraintSystem::<F>::new(SynthesisMode::Debug);
    circuit.generate_constraints(&mut cs)?;
    let unsatisfied_constraint = cs.which_is_unsatisfied();
    match unsatisfied_constraint {
        None => Ok(None),
        Some(name) => Ok(Some(name.into())),
    }
}

#[cfg(test)]
mod test {
    use crate::{debug_circuit, ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};
    use algebra::fields::tweedle::fr::Fr;
    use algebra::Field;
    use rand;

    struct MyCircuit<F: Field> {
        a: Option<F>,
        b: Option<F>,
        c: Option<F>,
    }

    impl<F: Field> ConstraintSynthesizer<F> for MyCircuit<F> {
        fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.alloc(|| "c", || self.c.ok_or(SynthesisError::AssignmentMissing))?;
            cs.enforce(
                || "multiplication constraint",
                |lc| lc + a,
                |lc| lc + b,
                |lc| lc + c,
            );
            Ok(())
        }
    }

    #[test]
    fn test_debug_circuit_satisfied() {
        let a: Fr = rand::random();
        let b: Fr = rand::random();
        let mut c = a.clone();
        c *= &b;
        let circuit = MyCircuit {
            a: Some(a),
            b: Some(b),
            c: Some(c),
        };
        let unsatisfied_constraint = debug_circuit(circuit).unwrap();
        assert!(unsatisfied_constraint.is_none());
    }

    #[test]
    fn test_debug_circuit_unsatisfied() {
        let a: Fr = rand::random();
        let b: Fr = rand::random();
        let mut c = a.clone();
        c *= &b;
        c += &b;
        let circuit = MyCircuit {
            a: Some(a),
            b: Some(b),
            c: Some(c),
        };
        let unsatisfied_constraint = debug_circuit(circuit).unwrap();
        assert!(unsatisfied_constraint.is_some());
        assert_eq!(unsatisfied_constraint.unwrap(), "multiplication constraint");
    }
}
