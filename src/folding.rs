use std::f32::consts::E;
use std::ops;

use rand_core::{RngCore, OsRng};
use nova_snark::r1cs::{
    RelaxedR1CSWitness, RelaxedR1CSInstance, R1CSWitness, R1CSInstance,
    R1CSShape,
};
use nova_snark::{Group, Commitment, CommitmentKey};
use ff::{
  derive::byteorder::{ByteOrder, LittleEndian},
  Field, PrimeField, PrimeFieldBits,
};

use crate::extraction::*;

#[derive(Clone)]
enum FoldingProverMessage<G: Group> {
    R1 { T_cm: Commitment<G> },
    R2 { folded_witness: RelaxedR1CSWitness<G> }
}

#[derive(Clone)]
enum FoldingVerifierMessage<G: Group> {
    R2 { r: G::Scalar }
}

#[derive(Clone)]
struct FoldingState<G: Clone + Group> {
    instance: <FoldingState<G> as ProtocolState>::Instance,
    witness: <FoldingState<G> as ProtocolState>::Witness,
    round: usize,
    transcript: Transcript<FoldingProverMessage<G>, FoldingVerifierMessage<G>>,
    t: Option<Vec<<G as Group>::Scalar>>
}

#[derive(Clone)]
struct FoldingInstance<G: Group> {
    ck: CommitmentKey<G>,
    shape: R1CSShape<G>,
    u1: RelaxedR1CSInstance<G>,
    u2: R1CSInstance<G>
}

#[derive(Clone)]
struct FoldingWitness<G: Group> {
    w1: RelaxedR1CSWitness<G>,
    w2: R1CSWitness<G>
}

#[derive(Clone)]
struct FoldingExtractor { }

impl<G: Clone + Group> ProtocolState for FoldingState<G> {
    type Instance = FoldingInstance<G>;
    type Witness = FoldingWitness<G>;
    type ProverMessage = FoldingProverMessage<G>;
    type VerifierMessage = FoldingVerifierMessage<G>;

    fn new(instance: &Self::Instance, witness: &Self::Witness) -> FoldingState<G> {
        FoldingState {
            instance: instance.clone(),
            witness: witness.clone(),
            round: 0,
            transcript: Transcript {
                prover_messages: vec![],
                verifier_messages: vec![],
            },
            t: None
        }
    }

    fn advance_one_round(&mut self) {
        if self.round == 0 {
            // Prover sends commitment to T.
            let (T, T_cm) = self.instance.shape.commit_T(
                &self.instance.ck, &self.instance.u1, &self.witness.w1,
                &self.instance.u2, &self.witness.w2
            ).unwrap();

            // Save T in the prover's state.
            self.t = Some(T);

            self.transcript.prover_messages.push(
                FoldingProverMessage::<G>::R1 { T_cm }
            )
        } else if self.round == 1 {
            // Verifier samples challenge r
            let r = G::Scalar::random(&mut OsRng);
            
            self.transcript.verifier_messages.push(
                FoldingVerifierMessage::<G>::R2 { r }
            );

            // Get T_cm
            let T_cm = match self.transcript.prover_messages[0] {
                FoldingProverMessage::<G>::R1 { T_cm: T_cm } => T_cm,
                _ => panic!("there is bug.")
            };

            // Prover and verifier both compute the folded instance
            let u = self.instance.u1.fold(&self.instance.u2, &T_cm, &r).unwrap();

            // Prover outputs the folded witness
            let w = self.witness.w1.fold(&self.witness.w2, self.t.as_ref().unwrap(), &r).unwrap();
            self.transcript.prover_messages.push( FoldingProverMessage::<G>::R2 { folded_witness: w.clone() } );

            // Verifier checks the folded witness satisfies the folded instance
            if !self.instance.shape.is_sat_relaxed(&self.instance.ck, &u, &w).is_ok() {
                panic!("folded witness no satisfy");
            }
        } else {
            panic!("Not that many rounds!");
        }

        self.round += 1;
    }

    fn transcript(&self) -> Transcript<Self::ProverMessage, Self::VerifierMessage> {
        self.transcript.clone()
    }

    fn is_aborted(&self) -> bool {
        // The protocol never aborts.
        false
    }

    fn is_complete(&self) -> bool {
        self.round == 2
    }

    fn current_round(&self) -> usize {
        self.round
    }

}

#[derive(Clone)]
struct ScalarVec<G: Group> {
    v: Vec<<G as Group>::Scalar>
}

impl<G: Group> ops::Add<ScalarVec<G>> for ScalarVec<G> {
    type Output = ScalarVec<G>;

    fn add(self, _rhs: ScalarVec<G>) -> ScalarVec<G> {
        assert!(self.v.len() == _rhs.v.len());

        let mut output = vec![<G as Group>::Scalar::zero(); self.v.len()];
        for i in 0..self.v.len() {
            output[i] = self.v[i] + _rhs.v[i];
        }

        ScalarVec{ v: output }
    }
}

impl<G: Group> ops::Sub<ScalarVec<G>> for ScalarVec<G> {
    type Output = Self;

    fn sub(self, _rhs: Self) -> Self {
        assert!(self.v.len() == _rhs.v.len());

        let mut output = vec![<G as Group>::Scalar::zero(); self.v.len()];
        for i in 0..self.v.len() {
            output[i] = self.v[i] - _rhs.v[i];
        }

        Self { v: output }
    }
}

impl<G: Group> ops::Mul<<G as Group>::Scalar> for ScalarVec<G> {
    type Output = Self;

    fn mul(self, _rhs: <G as Group>::Scalar) -> Self {
        let mut output = vec![<G as Group>::Scalar::zero(); self.v.len()];
        for i in 0..self.v.len() {
            output[i] = self.v[i] * _rhs;
        }

        Self { v: output }
    }
}

// impl<G: Group> ops::Mul<ScalarVec<G>> for <G as Group>::Scalar {
//     type Output = ScalarVec<G>;
// 
//     fn mul(self, _rhs: <G as Group>::Scalar) -> Self {
// 
//         let mut output = vec![<G as Group>::Scalar::zero(); _rhs.v.len()];
//         for i in 0..self.v.len() {
//             output[i] = self * _rhs.v[i];
//         }
// 
//         ScalarVec<G> { v: output }
//     }
// 
// }

impl<G: Clone + Group> Extractor<FoldingState<G>> for FoldingExtractor {
    fn extract(root: TranscriptTreeNode<<FoldingState<G> as ProtocolState>::ProverMessage, <FoldingState<G> as ProtocolState>::VerifierMessage>) -> <FoldingState<G> as ProtocolState>::Witness {
        assert!(root.children.len() == 1);
        assert!(root.children[0].children.len() == 3);

        let W: Vec<ScalarVec<G>> = vec![
            match &root.children[0].children[0].transcript.prover_messages[1] { 
                FoldingProverMessage::R2 { folded_witness: fw } => ScalarVec { v: fw.W.clone() },
                _ => panic!()
            },
            match &root.children[0].children[1].transcript.prover_messages[1] { 
                FoldingProverMessage::R2 { folded_witness: fw } => ScalarVec { v: fw.W.clone() },
                _ => panic!()
            },
            match &root.children[0].children[2].transcript.prover_messages[1] { 
                FoldingProverMessage::R2 { folded_witness: fw } => ScalarVec { v: fw.W.clone() },
                _ => panic!()
            }
        ];

        let EE: Vec<ScalarVec<G>> = vec![
            match &root.children[0].children[0].transcript.prover_messages[1] { 
                FoldingProverMessage::R2 { folded_witness: fw } => ScalarVec { v: fw.E.clone() },
                _ => panic!()
            },
            match &root.children[0].children[1].transcript.prover_messages[1] { 
                FoldingProverMessage::R2 { folded_witness: fw } => ScalarVec { v: fw.E.clone() },
                _ => panic!()
            },
            match &root.children[0].children[2].transcript.prover_messages[1] { 
                FoldingProverMessage::R2 { folded_witness: fw } => ScalarVec { v: fw.E.clone() },
                _ => panic!()
            }
        ];

        let r = vec![
            match &root.children[0].children[0].transcript.verifier_messages[0] { 
                FoldingVerifierMessage::R2 { r } => r.clone(),
                _ => panic!()
            },
            match &root.children[0].children[1].transcript.verifier_messages[0] { 
                FoldingVerifierMessage::R2 { r } => r.clone(),
                _ => panic!()
            },
            match &root.children[0].children[2].transcript.verifier_messages[0] { 
                FoldingVerifierMessage::R2 { r } => r.clone(),
                _ => panic!()
            },
        ];

        let len_w = W[0].v.len();
        assert!(W[1].v.len() == len_w);
        assert!(W[2].v.len() == len_w);

        let W1 = (W[1].clone() * r[0] - W[0].clone() * r[1]) * (r[0] - r[1]).invert().unwrap();
        let W2 = (W[0].clone() - W[1].clone()) * (r[0] - r[1]).invert().unwrap();

        let qinv = ((r[0] - r[1]) * (r[0] - r[1]) * (r[1] - r[2])).invert().unwrap();

        let E1 = (
            EE[0].clone() * r[1] * r[2] * (r[1] - r[2]) +
            EE[1].clone() * r[0] * r[2] * (r[2] - r[0]) + 
            EE[2].clone() * r[0] * r[1] * (r[0] - r[1])
        ) * qinv;

        let E2 = (
            EE[0].clone() * (r[1] - r[2]) + EE[1].clone() * (r[2] - r[0]) + EE[2].clone() * (r[0] - r[1])
        ) * qinv;

        // Check that E is 0 in W2 (it's a strict R1CS instance)
        for i in 0..E2.v.len() {
            assert_eq!(E2.v[i], <G as Group>::Scalar::zero());
        }

        // TEMPORARY: same should be true of E1 since our example folds two strict relaxed instances
        for i in 0..E1.v.len() {
            assert_eq!(E1.v[i], <G as Group>::Scalar::zero());
        }

        FoldingWitness::<G> {
            w1: RelaxedR1CSWitness::<G> {
                W: W1.v,
                E: E1.v,
            },
            w2: R1CSWitness::<G> {
                W: W2.v,
            }
        }

    }

    fn required_arity(level: usize) -> usize {
        if level == 0 {
            1
        } else {
            3
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extraction::*;

    type G1 = pasta_curves::pallas::Point;
    type G2 = pasta_curves::vesta::Point;

    use nova_snark::gadgets::ecc::*;
    use nova_snark::gadgets::ecc::tests::*;
    use nova_snark::bellperson::{
        r1cs::{NovaShape, NovaWitness},
        {shape_cs::ShapeCS, solver::SatisfyingAssignment},
    };

    use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
        Assignment,
    },
    ConstraintSystem, SynthesisError,
    };

    fn get_instance_witness() -> (R1CSInstance<pasta_curves::Eq>, R1CSWitness<pasta_curves::Eq>) {
        // First create the shape
        let mut cs: ShapeCS<G2> = ShapeCS::new();
        let _ = synthesize_add_equal::<G1, _>(cs.namespace(|| "synthesize add equal"));
        println!("Number of constraints: {}", cs.num_constraints());
        let (shape, ck) = cs.r1cs_shape();

        // Then the satisfying assignment
        let mut cs: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
        let (a, e) = synthesize_add_equal::<G1, _>(cs.namespace(|| "synthesize add equal"));
        let (inst, witness) = cs.r1cs_instance_and_witness(&shape, &ck).unwrap();
        let a_p: Point<G1> = Point::new(
        a.x.get_value().unwrap(),
        a.y.get_value().unwrap(),
        a.is_infinity.get_value().unwrap() == <G1 as Group>::Base::one(),
        );
        let e_p: Point<G1> = Point::new(
        e.x.get_value().unwrap(),
        e.y.get_value().unwrap(),
        e.is_infinity.get_value().unwrap() == <G1 as Group>::Base::one(),
        );
        let e_new = a_p.add(&a_p);
        assert!(e_p.x == e_new.x && e_p.y == e_new.y);
        // Make sure that it is satisfiable
        assert!(shape.is_sat(&ck, &inst, &witness).is_ok());

        (inst, witness)
    }

    #[test]
    fn foo() {
        let mut cs: ShapeCS<G2> = ShapeCS::new();
        let _ = synthesize_add_equal::<G1, _>(cs.namespace(|| "synthesize add equal"));
        println!("Number of constraints: {}", cs.num_constraints());
        let (shape, ck) = cs.r1cs_shape();

        let (u1, w1) = get_instance_witness();
        let (u2, w2) = get_instance_witness();

        let u1r = RelaxedR1CSInstance::from_r1cs_instance(&ck, &shape, &u1);
        let w1r = RelaxedR1CSWitness::from_r1cs_witness(&shape, &w1);

        let instance = FoldingInstance::<G2> { ck: ck.clone(), shape: shape.clone(), u1: u1r.clone(), u2: u2.clone() };
        let witness = FoldingWitness::<G2> { w1: w1r.clone(), w2: w2.clone() };

        let root = FoldingState::<G2>::new(&instance, &witness);

        let tree = generate_tree::<FoldingState<G2>, FoldingExtractor>(root, 0);
        let extracted_witness = FoldingExtractor::extract(tree);

        assert_eq!(extracted_witness.w1, witness.w1);
        assert_eq!(extracted_witness.w2, witness.w2);

        assert!(shape.is_sat(&ck, &u2, &extracted_witness.w2).is_ok());
        assert!(shape.is_sat(&ck, &u1, &R1CSWitness::<G2> { W: extracted_witness.w1.W}).is_ok());

    }
}