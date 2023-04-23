pub trait ProtocolState : Clone {
    type Instance;
    type Witness;

    type ProverMessage;
    type VerifierMessage;

    fn new(instance: &Self::Instance, witness: &Self::Witness) -> Self;

    fn advance_one_round(&mut self);
    fn transcript(&self) -> Transcript<Self::ProverMessage, Self::VerifierMessage>;
    fn is_aborted(&self) -> bool;
    fn is_complete(&self) -> bool;
    fn current_round(&self) -> usize;
}
#[derive(Clone)]
pub struct Transcript<P, V> {
    pub prover_messages: Vec<P>,
    pub verifier_messages: Vec<V>
}

pub struct TranscriptTreeNode<P, V> {
    pub transcript: Transcript<P, V>,
    pub children: Vec<Self>,
}

pub fn generate_tree<P: ProtocolState, E: Extractor<P>>(root: P, cur_level: usize) -> TranscriptTreeNode<P::ProverMessage, P::VerifierMessage> {
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

pub trait Extractor<P: ProtocolState> {
    fn extract(root: TranscriptTreeNode<P::ProverMessage, P::VerifierMessage>) -> P::Witness;
    fn required_arity(level: usize) -> usize;
}