//! Simple Marlin "proof carrying data". This corresponds to non-recursive applications.
use crate::darlin::{
    accumulators::{
        dlog::DLogItemAccumulator,
        ItemAccumulator,
    },
    pcd::{error::PCDError, PCD},
    DomainExtendedIpaPc,
};
use algebra::{serialize::*, SemanticallyValid, GroupVec};
use bench_utils::*;
use fiat_shamir::FiatShamirRng;
use marlin::{Marlin, Proof, VerifierKey, IOP, iop::indexer::IndexInfo};
use poly_commit::{
    ipa_pc::{InnerProductArgPC, VerifierKey as DLogVerifierKey, IPACurve, Proof as DLogProof},
    DomainExtendedPolynomialCommitment, DomainExtendedMultiPointProof, BDFGMultiPointProof, PolynomialCommitment,
};
use derivative::Derivative;
use std::{marker::PhantomData, collections::HashMap};
use std::ops::{Deref, DerefMut};
use num_traits::Zero;

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct MarlinProof<G: IPACurve, FS: FiatShamirRng + 'static>(
    pub Proof<G, DomainExtendedIpaPc<G, FS>>,
);

#[derive(Clone)]
pub struct DefaultMarlinProofConfig {
    zk: bool,
    segment_size: usize,
    num_inputs: usize,
    num_evaluations: usize,
    num_rounds: usize,
    comms_per_round: Vec<usize>,
    h: usize,
    k: usize,
    segments_num: HashMap<String, usize>
}

impl DefaultMarlinProofConfig {
    pub fn new<G: IPACurve>(
        info: IndexInfo<G::BaseField>,
        segment_size: usize,
        zk: bool,
    ) -> Self 
    {
        // Derive config from IndexInfo
        let zk_bound: usize = if zk { 1 } else { 0 };
        let segment_size = segment_size.next_power_of_two();
        
        let num_inputs = info.num_inputs.next_power_of_two();
        let h = std::cmp::max(
            info.num_constraints.next_power_of_two(),
            (info.num_witness + info.num_inputs).next_power_of_two(),
        );
        let k = info.num_non_zero.next_power_of_two();
        
        // Protocol-related config data
        let num_rounds = 3;
        let comms_per_round = vec![3, 2, 2];
        
        let num_evaluations = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len()
            + IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len()
            + 2; // boundary polynomials are evaluated at two different points
        #[cfg(feature = "circuit-friendly")]
        let num_evaluations = num_evaluations + 1; // vanishing poly v_h evaluated at two different points.

        // Compute number of segments for each poly to commit
        let mut segments_num = HashMap::new();

        // First round commitments
        segments_num.insert("w".to_string(), ((h + 2 * zk_bound - num_inputs) as f64 / segment_size as f64).ceil() as usize);
        
        let y_a_b_segs = ((h + 2 * zk_bound) as f64 / segment_size as f64).ceil() as usize;
        segments_num.insert("y_a".to_string(), y_a_b_segs);
        segments_num.insert("y_b".to_string(), y_a_b_segs);

        // Second round commitments
        segments_num.insert("u_1".to_string(), ((h + 3 * zk_bound) as f64 / segment_size as f64).ceil() as usize);
        segments_num.insert("h_1".to_string(), ((2 * h + 4 * zk_bound - 2) as f64 / segment_size as f64).ceil() as usize);

        // Third round commitments
        segments_num.insert("u_2".to_string(), (k as f64 / segment_size as f64).ceil() as usize);
        segments_num.insert("h_2".to_string(), ((3 * k - 3) as f64 / segment_size as f64).ceil() as usize);

        // l_vec and r_vec
        segments_num.insert("l_vec".to_string(), segment_size);
        segments_num.insert("r_vec".to_string(), segment_size);

        // Batching polynomial commitment
        segments_num.insert("h".to_string(), ((3 * k - 4) as f64 / segment_size as f64).ceil() as usize);

        DefaultMarlinProofConfig {
            zk,
            segment_size,
            num_inputs,
            num_evaluations,
            num_rounds,
            comms_per_round,
            h,
            k,
            segments_num
        }
    }
}

impl<G: IPACurve, FS: FiatShamirRng> MarlinProof<G, FS> {
    /// Get a default instantiation of this proof, sized according to the supplied config.
    pub fn get_default_sized(config: DefaultMarlinProofConfig) -> Self
    {
        // Initialize commitments
        let commitments = vec![
            vec![
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("w").unwrap()]),
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("y_a").unwrap()]),
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("y_b").unwrap()])
            ],
            vec![
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("u_1").unwrap()]),
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("h_1").unwrap()])
            ],
            vec![
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("u_2").unwrap()]),
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("h_2").unwrap()])
            ]
        ];

        // Initialize evaluations
        let evaluations = vec![G::ScalarField::zero(); config.num_evaluations];

        // Initialize DLOG proof
        let pc_proof = DLogProof::<G> {
            l_vec: vec![G::zero(); config.segment_size],
            r_vec: vec![G::zero(); config.segment_size],
            final_comm_key: G::zero(),
            c: G::ScalarField::zero(),
            hiding_comm: if config.zk { Some(G::zero()) } else { None },
            rand: if config.zk { Some(G::ScalarField::zero()) } else { None },
        };

        // Initialize DLog multi point proof
        let h_comm = GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("h").unwrap()]);
        let multi_pc_proof = DomainExtendedMultiPointProof::<G, DLogProof<G>>::new(pc_proof, h_comm);

        // Return proof
        MarlinProof(Proof::<G, DomainExtendedIpaPc<G, FS>>::new(
            commitments,
            evaluations,
            multi_pc_proof,
        ))
    }

    /// Pad `self` to a proof sized according to the supplied inputs.
    /// Padding values are default ones. 
    pub fn pad_to_default_size(&mut self, config: DefaultMarlinProofConfig) -> Result<(), PCDError> 
    {
        // Pre-checks:
        // Return Error if trying to pad a proof which doesn't have the same number
        // of commitments and/or evaluations (it means it belongs to a different protocol)
        if self.commitments.len() != config.num_rounds ||
            vec![self.commitments[0].len(), self.commitments[1].len(), self.commitments[2].len()] != config.comms_per_round ||
            self.evaluations.len() != config.num_evaluations
        {
            return Err(PCDError::Other("Trying to pad a proof belonging to a different protocol !".to_string()));
        }

        // Return Error if trying to compare two proofs that have not the same zk property.
        // TODO: Do we really need this ? Can we assume having always zk proofs and verify them as such ?
        if self.pc_proof.proof.hiding_comm.is_some() != config.zk || self.pc_proof.proof.rand.is_some() != config.zk 
        {
            return Err(PCDError::Other("Hiding data must not be present if zk is disabled and viceversa !".to_string()));
        }

        // Pad `gv` to the expected segment size of `param`, as defined in `config.segments_num`.
        // Returns Error if `gv` is bigger than the retrieved segment num or if `param` doesn't exist.
        let pad_if_needed = 
            |gv: &mut Vec<G>, param: &str| -> Result<(), PCDError>
            {
                let expected_num_segs = *config
                    .segments_num
                    .get(param)
                    .ok_or(PCDError::Other(format!("Could not find param {:?} in config.segments_num !", param)))?;

                if gv.len() > expected_num_segs {
                    return Err(PCDError::Other(format!("Proof is bigger than default size one for param {:?} !", param)));
                }

                gv.resize(expected_num_segs, G::zero());

                Ok(())
            };

        // Pad commitments if needed
        pad_if_needed(&mut self.commitments[0][0].0, "w")?;
        pad_if_needed(&mut self.commitments[0][1].0, "y_a")?;
        pad_if_needed(&mut self.commitments[0][2].0, "y_b")?;
        pad_if_needed(&mut self.commitments[1][0].0, "u_1")?;
        pad_if_needed(&mut self.commitments[1][1].0, "h_1")?;
        pad_if_needed(&mut self.commitments[2][0].0, "u_2")?;
        pad_if_needed(&mut self.commitments[2][1].0, "h_2")?;


        // Pad DLOG proof if needed
        pad_if_needed(&mut self.pc_proof.proof.l_vec, "l_vec")?;
        pad_if_needed(&mut self.pc_proof.proof.r_vec, "r_vec")?;

        // Pad DLog multi point proof if needed
        pad_if_needed(&mut self.pc_proof.h_commitment.0, "h")?;

        // Padding finished
        Ok(())
    }
}

impl<G: IPACurve, FS: FiatShamirRng> Deref for MarlinProof<G, FS> {
    type Target = Proof<G, DomainExtendedIpaPc<G, FS>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<G: IPACurve, FS: FiatShamirRng> DerefMut for MarlinProof<G, FS> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<G: IPACurve, FS: FiatShamirRng> SemanticallyValid for MarlinProof<G, FS> {
    fn is_valid(&self) -> bool {
        // Check commitments number and validity
        let num_rounds = 3;
        let comms_per_round = vec![3, 2, 2];

        // Check commitments are grouped into correct num_rounds
        if self.commitments.len() != num_rounds {
            return false;
        };

        // Check that each round has the expected number of commitments
        for i in 0..comms_per_round.len() {
            if self.commitments[i].len() != comms_per_round[i] {
                return false;
            };
        }

        // Check evaluations num
        let num_polys = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len()
            + IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len();
        let evaluations_num = num_polys + 2;
        #[cfg(feature = "circuit-friendly")]
        let evaluations_num = evaluations_num + 1; // Vanishing poly v_h is evaluated at two points.

        self.commitments.is_valid() &&  // Check that each commitment is valid
            self.evaluations.len() == evaluations_num && // Check correct number of evaluations
            self.evaluations.is_valid() && // Check validity of each evaluation
            // Check opening proof
            self.pc_proof.is_valid()
    }
}

const SIMPLE_MARLIN_PCD_IDENTIFIER: &str = "SimpleMarlin";

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct SimpleMarlinPCD<'a, G: IPACurve, FS: FiatShamirRng + 'static> {
    pub proof: MarlinProof<G, FS>,
    pub usr_ins: Vec<G::ScalarField>,
    _lifetime: PhantomData<&'a ()>,
}

/// As every PCD, the `SimpleMarlinPCD` comes as a proof plus "statement".
impl<'a, G, FS> SimpleMarlinPCD<'a, G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng + 'a,
{
    pub fn new(
        // A normal (coboundary) Marlin proof
        proof: MarlinProof<G, FS>,
        // The "statement" of the proof. Typically the full public inputs
        usr_ins: Vec<G::ScalarField>,
    ) -> Self {
        Self {
            proof,
            usr_ins,
            _lifetime: PhantomData,
        }
    }
}

/// To verify the PCD of a simple Marlin we only need the `MarlinVerifierKey` (or, the
/// IOP verifier key) of the circuit, and the two dlog committer keys for G1 and G2.
pub struct SimpleMarlinPCDVerifierKey<'a, G: IPACurve, FS: FiatShamirRng + 'static>(
    pub &'a MarlinVerifierKey<G, FS>,
    pub &'a DLogVerifierKey<G>,
);

impl<'a, G: IPACurve, FS: FiatShamirRng> AsRef<DLogVerifierKey<G>>
    for SimpleMarlinPCDVerifierKey<'a, G, FS>
{
    fn as_ref(&self) -> &DLogVerifierKey<G> {
        &self.1
    }
}

impl<'a, G, FS> PCD for SimpleMarlinPCD<'a, G, FS>
where
    G: IPACurve,
    FS: FiatShamirRng + 'static,
{
    type PCDAccumulator = DLogItemAccumulator<G, FS>;
    type PCDVerifierKey = SimpleMarlinPCDVerifierKey<'a, G, FS>;

    fn succinct_verify(
        &self,
        vk: &Self::PCDVerifierKey,
    ) -> Result<<Self::PCDAccumulator as ItemAccumulator>::Item, PCDError> {
        let succinct_time = start_timer!(|| "Marlin succinct verifier");

        // Verify the IOP/AHP
        let (query_map, evaluations, labeled_comms, mut fs_rng) = Marlin::<
            G,
            DomainExtendedIpaPc<G, FS>,
        >::verify_iop(
            &vk.1,
            &vk.0,
            self.usr_ins.as_slice(),
            &self.proof,
        )
        .map_err(|e| {
            end_timer!(succinct_time);
            PCDError::FailedSuccinctVerification(format!("{:?}", e))
        })?;

        // record evaluations and sample new challenge
        fs_rng.record(self.proof.evaluations.clone()).map_err(|e| {
            end_timer!(succinct_time);
            PCDError::FailedSuccinctVerification(format!("{:?}", e))
        })?;

        // Succinct verify DLOG proof
        let verifier_state = DomainExtendedPolynomialCommitment::<G, InnerProductArgPC::<G, FS>>::succinct_multi_point_multi_poly_verify(
            &vk.1,
            &labeled_comms,
            &query_map,
            &evaluations,
            &self.proof.pc_proof,
            &mut fs_rng,
        ).map_err(|e| {
            end_timer!(succinct_time);
            PCDError::FailedSuccinctVerification(e.to_string())
        })?;

        if verifier_state.is_none() {
            end_timer!(succinct_time);
            Err(PCDError::FailedSuccinctVerification(
                "Succinct verify failed".to_owned(),
            ))?
        }

        // Successfull verification: return current accumulator
        let acc = verifier_state.unwrap();

        end_timer!(succinct_time);
        Ok(acc)
    }

    fn get_id() -> String {
        SIMPLE_MARLIN_PCD_IDENTIFIER.to_string()
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
pub struct MarlinVerifierKey<G: IPACurve, FS: FiatShamirRng + 'static>(
    pub VerifierKey<G, DomainExtendedIpaPc<G, FS>>,
);

impl<G: IPACurve, FS: FiatShamirRng> Deref for MarlinVerifierKey<G, FS> {
    type Target = VerifierKey<G, DomainExtendedIpaPc<G, FS>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<G: IPACurve, FS: FiatShamirRng> DerefMut for MarlinVerifierKey<G, FS> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Clone)]
pub struct DefaultMarlinVkConfig {
    segment_size: usize,
    x: usize,
    k: usize,
}

impl DefaultMarlinVkConfig {
    pub fn new<G: IPACurve>(
        info: IndexInfo<G::BaseField>,
        segment_size: usize,
    ) -> Self 
    {
        let segment_size = segment_size.next_power_of_two();
        let x = info.num_inputs.next_power_of_two();
        let k = info.num_non_zero.next_power_of_two();

        DefaultMarlinVkConfig {
            segment_size,
            x,
            k,
        }
    }
}

impl<G: IPACurve, FS: FiatShamirRng> MarlinVerifierKey<G, FS> {
    /// Get a default instantiation of this vk, sized according to the supplied config.
    pub fn get_default_sized(config: DefaultMarlinVkConfig) -> Self
    {
        // Initialize commitments
        let indexer_polys_num_segs = (config.k as f64 / config.segment_size as f64).ceil() as usize;
        
        let commitments = vec![
            vec![
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("w").unwrap()]),
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("y_a").unwrap()]),
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("y_b").unwrap()])
            ],
            vec![
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("u_1").unwrap()]),
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("h_1").unwrap()])
            ],
            vec![
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("u_2").unwrap()]),
                GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("h_2").unwrap()])
            ]
        ];

        // Initialize evaluations
        let evaluations = vec![G::ScalarField::zero(); config.num_evaluations];

        // Initialize DLOG proof
        let pc_proof = DLogProof::<G> {
            l_vec: vec![G::zero(); config.segment_size],
            r_vec: vec![G::zero(); config.segment_size],
            final_comm_key: G::zero(),
            c: G::ScalarField::zero(),
            hiding_comm: if config.zk { Some(G::zero()) } else { None },
            rand: if config.zk { Some(G::ScalarField::zero()) } else { None },
        };

        // Initialize DLog multi point proof
        let h_comm = GroupVec::<G>::new(vec![G::zero(); *config.segments_num.get("h").unwrap()]);
        let multi_pc_proof = DomainExtendedMultiPointProof::<G, DLogProof<G>>::new(pc_proof, h_comm);

        // Return proof
        MarlinProof(Proof::<G, DomainExtendedIpaPc<G, FS>>::new(
            commitments,
            evaluations,
            multi_pc_proof,
        ))
    }

    /// Pad `self` to a proof sized according to the supplied inputs.
    /// Padding values are default ones. 
    pub fn pad_to_default_size(&mut self, config: DefaultMarlinProofConfig) -> Result<(), PCDError> 
    {
        // Pre-checks:
        // Return Error if trying to pad a proof which doesn't have the same number
        // of commitments and/or evaluations (it means it belongs to a different protocol)
        if self.commitments.len() != config.num_rounds ||
            vec![self.commitments[0].len(), self.commitments[1].len(), self.commitments[2].len()] != config.comms_per_round ||
            self.evaluations.len() != config.num_evaluations
        {
            return Err(PCDError::Other("Trying to pad a proof belonging to a different protocol !".to_string()));
        }

        // Return Error if trying to compare two proofs that have not the same zk property.
        // TODO: Do we really need this ? Can we assume having always zk proofs and verify them as such ?
        if self.pc_proof.proof.hiding_comm.is_some() != config.zk || self.pc_proof.proof.rand.is_some() != config.zk 
        {
            return Err(PCDError::Other("Hiding data must not be present if zk is disabled and viceversa !".to_string()));
        }

        // Pad `gv` to the expected segment size of `param`, as defined in `config.segments_num`.
        // Returns Error if `gv` is bigger than the retrieved segment num or if `param` doesn't exist.
        let pad_if_needed = 
            |gv: &mut Vec<G>, param: &str| -> Result<(), PCDError>
            {
                let expected_num_segs = *config
                    .segments_num
                    .get(param)
                    .ok_or(PCDError::Other(format!("Could not find param {:?} in config.segments_num !", param)))?;

                if gv.len() > expected_num_segs {
                    return Err(PCDError::Other(format!("Proof is bigger than default size one for param {:?} !", param)));
                }

                gv.resize(expected_num_segs, G::zero());

                Ok(())
            };

        // TODO: Be careful about h_size_inv and k_size_inv.
        // Pad commitments if needed
        pad_if_needed(&mut self.commitments[0][0].0, "w")?;
        pad_if_needed(&mut self.commitments[0][1].0, "y_a")?;
        pad_if_needed(&mut self.commitments[0][2].0, "y_b")?;
        pad_if_needed(&mut self.commitments[1][0].0, "u_1")?;
        pad_if_needed(&mut self.commitments[1][1].0, "h_1")?;
        pad_if_needed(&mut self.commitments[2][0].0, "u_2")?;
        pad_if_needed(&mut self.commitments[2][1].0, "h_2")?;


        // Pad DLOG proof if needed
        pad_if_needed(&mut self.pc_proof.proof.l_vec, "l_vec")?;
        pad_if_needed(&mut self.pc_proof.proof.r_vec, "r_vec")?;

        // Pad DLog multi point proof if needed
        pad_if_needed(&mut self.pc_proof.h_commitment.0, "h")?;

        // Padding finished
        Ok(())
    }
}