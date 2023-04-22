use ark_bn254::{Fr as F, G1Affine};
use ark_ec::AffineRepr;
use ark_ff::Field;
use ark_std::{test_rng, UniformRand};
use rand_core::{RngCore, OsRng};

trait ProtocolState : Clone {
    type Instance;
    type Witness;

    type ProverMessage;
    type VerifierMessage;

    fn new(instance: Self::Instance, witness: Self::Witness) -> Self;

    fn advance_one_round(&mut self);
    fn transcript(&self) -> Transcript<Self::ProverMessage, Self::VerifierMessage>;
    fn is_aborted(&self) -> bool;
    fn is_complete(&self) -> bool;
    fn current_round(&self) -> usize;
}
#[derive(Clone)]
struct Transcript<P, V> {
    prover_messages: Vec<P>,
    verifier_messages: Vec<V>
}

struct TranscriptTreeNode<P, V> {
    transcript: Transcript<P, V>,
    children: Vec<Self>,
}

fn generate_tree<P: ProtocolState, E: Extractor<P>>(root: P, cur_level: usize) -> TranscriptTreeNode<P::ProverMessage, P::VerifierMessage> {
    let mut tr_root = TranscriptTreeNode {
        transcript: root.transcript(),
        children: vec![]
    };

    // If the protocol is finished and validates, we are a leaf.
    if root.is_complete() {
        return tr_root;
    }

    // Otherwise, advance one step, branching as many times as we need at this round.
    let needed = E::required_arity(cur_level);

    while tr_root.children.len() < needed {
        let mut child = root.clone();
        child.advance_one_round();

        // If the protocol fails, try again.
        if child.is_aborted() {
            continue;
        }
        tr_root.children.push(generate_tree::<P, E>(child, cur_level + 1));
    }
    
    tr_root
}

trait Extractor<P: ProtocolState> {
    fn extract(root: TranscriptTreeNode<P::ProverMessage, P::VerifierMessage>) -> P::Witness;
    fn required_arity(level: usize) -> usize;
}

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

    fn new(instance: (), witness: F) -> SchnorrState {
        SchnorrState {
            x: witness,
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
            panic!("schnorr does not have that many rounds");
        }

        self.round += 1;
    }

    fn transcript(&self) -> Transcript<Self::ProverMessage, Self::VerifierMessage> {
        self.transcript.clone()
    }

    fn is_aborted(&self) -> bool {
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

fn extract() {
    let mut rng = test_rng();
    let g = G1Affine::generator();
    let x = F::rand(&mut rng);

    // Round 1:
    // - sample random r
    // - compute u = [r]G
    let r = F::rand(&mut rng);

    // First execution
    // Round 2:
    // - verifier challenge c_1
    let c_1 = F::rand(&mut rng);

    // Round 3:
    // - z_1 = r + x * c_1
    let z_1 = r + x * c_1;

    // Rewind

    // Second execution
    // Round 2:
    // - verifier challenge c_2
    let c_2 = F::rand(&mut rng);
    assert_ne!(c_1, c_2);

    // Round 3:
    // - z_2 = r + x * c_2
    let z_2 = r + x * c_2;

    // x = (z_1 - z_2) / (c_1 - c_2)
    let extracted_x = (z_1 - z_2) * (c_1 - c_2).inverse().unwrap();
    assert_eq!(x, extracted_x);
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn foo() {
        let mut rng = test_rng();
        let x = F::rand(&mut rng);

        let root = SchnorrState::new((), x);

        let tree = generate_tree::<SchnorrState, SchnorrExtractor>(root, 0);

        let extracted_x = SchnorrExtractor::extract(tree);

        assert_eq!(x, extracted_x);
    }
}
