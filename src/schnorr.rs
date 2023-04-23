use ark_bn254::{Fr as F, G1Affine};
use ark_ec::AffineRepr;
use ark_ff::Field;
use ark_std::{test_rng, UniformRand};
use rand_core::{RngCore, OsRng};

use crate::extraction::*;

#[derive(Clone)]
struct SchnorrState {
    x: F,
    r: F,
    c: F,
    z: F,
    round: usize,
    transcript: Transcript<F, F>,
}

#[derive(Clone)]
struct SchnorrExtractor {
}

impl ProtocolState for SchnorrState {
    type Instance = ();
    type Witness = F;
    type ProverMessage = F;
    type VerifierMessage = F;

    fn new(instance: &(), witness: &F) -> SchnorrState {
        SchnorrState {
            x: witness.clone(),
            r: F::from(0),
            c: F::from(0),
            z: F::from(0),
            round: 0,
            transcript: Transcript {
                prover_messages: vec![],
                verifier_messages: vec![],
            },
        }
    }

    fn advance_one_round(&mut self) {
        let g = G1Affine::generator();

        if self.round == 0 {
            self.r = F::rand(&mut OsRng);
            println!("r: {:?}", self.r);
            // FIXME: we don't actually need U, the type F is wrong
            self.transcript.prover_messages.push(F::from(0));
        } else if self.round == 1 {
            self.c = F::rand(&mut OsRng);
            self.transcript.verifier_messages.push(self.c);
            self.z = self.r + self.x * self.c;
            self.transcript.prover_messages.push(self.z);
            println!("c: {:?}", self.c);
            println!("z: {:?}", self.z);
        } else {
            panic!("Schnorr does not have that many rounds");
        }

        self.round += 1;
    }

    fn transcript(&self) -> Transcript<Self::ProverMessage, Self::VerifierMessage> {
        self.transcript.clone()
    }

    fn is_aborted(&self) -> bool {
        // TODO
        //OsRng.next_u32() % 100000 != 0
        // Schnorr prover never fails.
        false
    }

    fn is_complete(&self) -> bool {
        self.round == 2
    }

    fn current_round(&self) -> usize {
        self.round
    }

}

impl Extractor<SchnorrState> for SchnorrExtractor {
    fn extract(root: TranscriptTreeNode<<SchnorrState as ProtocolState>::ProverMessage, <SchnorrState as ProtocolState>::VerifierMessage>) -> <SchnorrState as ProtocolState>::Witness {
        assert!(root.children.len() == 1);

        assert!(root.children[0].children.len() == 2);

        let z_1 = root.children[0].children[0].transcript.prover_messages[1];
        let z_2 = root.children[0].children[1].transcript.prover_messages[1];

        let c_1 = root.children[0].children[0].transcript.verifier_messages[0];
        let c_2 = root.children[0].children[1].transcript.verifier_messages[0];

        println!("z_1: {:?}", z_1);
        println!("z_2: {:?}", z_2);
        println!("c_1: {:?}", c_1);
        println!("c_2: {:?}", c_2);

        assert_ne!(c_1, c_2); // TODO: make the tree generator logic smart enough to prevent this?
        
        let extracted_x = (z_1 - z_2) * (c_1 - c_2).inverse().unwrap();

        extracted_x
    }

    fn required_arity(level: usize) -> usize {
        if level == 0 {
            1
        } else {
            2
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extraction::*;

    #[test]
    fn foo() {
        let x = F::rand(&mut OsRng);

        let root = SchnorrState::new(&(), &x);

        let tree = generate_tree::<SchnorrState, SchnorrExtractor>(root, 0);

        let extracted_x = SchnorrExtractor::extract(tree);

        assert_eq!(x, extracted_x);
    }
}