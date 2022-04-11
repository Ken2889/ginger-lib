use crate::{
    BDFGMultiPointProof, DomainExtendedPolynomialCommitment, MultiPointProofGadget,
    PolynomialCommitment, PolynomialCommitmentVerifierGadget,
};
use algebra::{Group, PrimeField};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::groups::group_vec::GroupGadgetVec;
use r1cs_std::prelude::AllocGadget;
use std::borrow::Borrow;
#[cfg(feature = "boneh-with-single-point-batch")]
use r1cs_std::boolean::Boolean;
#[cfg(feature = "boneh-with-single-point-batch")]
use algebra::ToBits;

/// Gadget for multi-point proof for domain extended poly-commit verifier gadget
pub struct DomainExtendedMultiPointProofGadget<
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G, Commitment = G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
> {
    proof: PCG::ProofGadget,
    h_commitment: GroupGadgetVec<ConstraintF, PC::Commitment, PCG::CommitmentGadget>,
    #[cfg(feature = "boneh-with-single-point-batch")]
    evaluations: Vec<Vec<Boolean>>,
}

impl<ConstraintF, G, PC, PCG>
    AllocGadget<
        <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::MultiPointProof,
        ConstraintF,
    > for DomainExtendedMultiPointProofGadget<ConstraintF, G, PC, PCG>
where
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: 'static + PolynomialCommitment<G, Commitment = G>,
    PCG: 'static + PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<
            <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::MultiPointProof,
        >,
    {
        let t = f()?;
        let mpp = t.borrow();

        let proof =
            PCG::ProofGadget::alloc(cs.ns(|| "alloc single point proof"), || Ok(mpp.get_proof()))?;
        let h_commitment =
            GroupGadgetVec::<ConstraintF, PC::Commitment, PCG::CommitmentGadget>::alloc(
                cs.ns(|| "alloc h-commitment for multi-point proof"),
                || Ok(mpp.get_h_commitment().clone()),
            )?;

        #[cfg(not(feature = "boneh-with-single-point-batch"))]
            return Ok(
            Self{
                proof,
                h_commitment,
            }
        );

        #[cfg(feature = "boneh-with-single-point-batch")]
        return {
            let mut evaluations = Vec::with_capacity(mpp.evaluations.len());
            for (i, value) in mpp.evaluations.iter().enumerate() {
                evaluations.push(Vec::<Boolean>::alloc(cs.ns(|| format!("alloc evaluation {} for multi-point proof", i)), || {
                    Ok(value.write_bits())
                })?);
            }

            Ok(Self {
                proof,
                h_commitment,
                evaluations,
            })
        };
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<
            <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::MultiPointProof,
        >,
    {
        let t = f()?;
        let mpp = t.borrow();

        let proof = PCG::ProofGadget::alloc_input(cs.ns(|| "alloc single point proof"), || {
            Ok(mpp.get_proof())
        })?;
        let h_commitment =
            GroupGadgetVec::<ConstraintF, PC::Commitment, PCG::CommitmentGadget>::alloc_input(
                cs.ns(|| "alloc h-commitment for multi-point proof"),
                || Ok(mpp.get_h_commitment().clone()),
            )?;

        #[cfg(not(feature = "boneh-with-single-point-batch"))]
        return Ok(
            Self{
                proof,
                h_commitment,
            }
        );

        #[cfg(feature = "boneh-with-single-point-batch")]
        return {
            let mut evaluations = Vec::with_capacity(mpp.evaluations.len());
            for (i, value) in mpp.evaluations.iter().enumerate() {
                evaluations.push(Vec::<Boolean>::alloc_input(cs.ns(|| format!("alloc evaluation {} for multi-point proof", i)), || {
                    Ok(value.write_bits())
                })?);
            }

            Ok(Self {
                proof,
                h_commitment,
                evaluations,
            })
        };
    }
}

impl<ConstraintF, G, PC, PCG>
    MultiPointProofGadget<
        ConstraintF,
        G,
        <DomainExtendedPolynomialCommitment<G, PC> as PolynomialCommitment<G>>::MultiPointProof,
    > for DomainExtendedMultiPointProofGadget<ConstraintF, G, PC, PCG>
where
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: 'static + PolynomialCommitment<G, Commitment = G>,
    PCG: 'static + PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
{
    type CommitmentGadget = GroupGadgetVec<ConstraintF, PC::Commitment, PCG::CommitmentGadget>;
    type ProofGadget = PCG::ProofGadget;

    fn get_proof(&self) -> &Self::ProofGadget {
        &self.proof
    }
    fn get_h_commitment(&self) -> &Self::CommitmentGadget {
        &self.h_commitment
    }

    #[cfg(feature = "boneh-with-single-point-batch")]
    fn get_evaluations(&self) -> &Vec<Vec<Boolean>> {
        &self.evaluations
    }
}
