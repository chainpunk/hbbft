use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Debug;

use crypto::{PublicKey, PublicKeySet, PublicKeyShare, SecretKey, SecretKeyShare};
use fault_log::FaultLog;

/// Message sent by a given source.
#[derive(Clone, Debug)]
pub struct SourcedMessage<M, N> {
    pub source: N,
    pub message: M,
}

/// Message destination can be either of the two:
///
/// 1) `All`: all remote nodes.
///
/// 2) `Node(id)`: remote node `id`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target<N> {
    All,
    Node(N),
}

impl<N> Target<N> {
    /// Returns a `TargetedMessage` with this target, and the given message.
    pub fn message<M>(self, message: M) -> TargetedMessage<M, N> {
        TargetedMessage {
            target: self,
            message,
        }
    }
}

/// Message with a designated target.
#[derive(Clone, Debug, PartialEq)]
pub struct TargetedMessage<M, N> {
    pub target: Target<N>,
    pub message: M,
}

impl<M, N> TargetedMessage<M, N> {
    /// Applies the given transformation of messages, preserving the target.
    pub fn map<T, F: Fn(M) -> T>(self, f: F) -> TargetedMessage<T, N> {
        TargetedMessage {
            target: self.target,
            message: f(self.message),
        }
    }
}

/// Result of one step of the local state machine of a distributed algorithm. Such a result should
/// be used and never discarded by the client of the algorithm.
#[must_use = "The algorithm step result must be used."]
pub struct Step<N, O>
where
    N: Clone,
{
    pub output: VecDeque<O>,
    pub fault_log: FaultLog<N>,
}

impl<N, O> Default for Step<N, O>
where
    N: Clone,
{
    fn default() -> Step<N, O> {
        Step {
            output: Default::default(),
            fault_log: FaultLog::default(),
        }
    }
}

impl<N, O> Step<N, O>
where
    N: Clone,
{
    pub fn new(output: VecDeque<O>, fault_log: FaultLog<N>) -> Self {
        Step { output, fault_log }
    }
}

/// A distributed algorithm that defines a message flow.
pub trait DistAlgorithm {
    /// Unique node identifier.
    type NodeUid: Debug + Clone + Ord + Eq;
    /// The input provided by the user.
    type Input;
    /// The output type. Some algorithms return an output exactly once, others return multiple
    /// times.
    type Output;
    /// The messages that need to be exchanged between the instances in the participating nodes.
    type Message: Debug;
    /// The errors that can occur during execution.
    type Error: Debug;

    /// Handles an input provided by the user, and returns
    fn input(
        &mut self,
        input: Self::Input,
    ) -> Result<Step<Self::NodeUid, Self::Output>, Self::Error>;

    /// Handles a message received from node `sender_id`.
    fn handle_message(
        &mut self,
        sender_id: &Self::NodeUid,
        message: Self::Message,
    ) -> Result<Step<Self::NodeUid, Self::Output>, Self::Error>;

    /// Returns a message that needs to be sent to another node.
    fn next_message(&mut self) -> Option<TargetedMessage<Self::Message, Self::NodeUid>>;

    /// Returns `true` if execution has completed and this instance can be dropped.
    fn terminated(&self) -> bool;

    /// Returns this node's own ID.
    fn our_id(&self) -> &Self::NodeUid;

    /// Returns an iterator over the outgoing messages.
    fn message_iter(&mut self) -> MessageIter<Self>
    where
        Self: Sized,
    {
        MessageIter { algorithm: self }
    }
}

/// An iterator over a distributed algorithm's outgoing messages.
pub struct MessageIter<'a, D: DistAlgorithm + 'a> {
    algorithm: &'a mut D,
}

impl<'a, D: DistAlgorithm + 'a> Iterator for MessageIter<'a, D> {
    type Item = TargetedMessage<D::Message, D::NodeUid>;

    fn next(&mut self) -> Option<Self::Item> {
        self.algorithm.next_message()
    }
}

/// Common data shared between algorithms: the validators' public IDs, key shares and public keys.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ValidatorMap<NodeUid> {
    num_nodes: usize,
    num_faulty: usize,
    public_key_set: PublicKeySet,
    public_key_shares: BTreeMap<NodeUid, PublicKeyShare>,
    public_keys: BTreeMap<NodeUid, PublicKey>,
    node_indices: BTreeMap<NodeUid, usize>,
}

impl<NodeUid: Serialize + Ord> Serialize for ValidatorMap<NodeUid> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.public_key_set, &self.public_keys).serialize(s)
    }
}

impl<'de, NodeUid: Deserialize<'de> + Ord + Clone> Deserialize<'de> for ValidatorMap<NodeUid> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (public_key_set, public_keys) =
            <(PublicKeySet, BTreeMap<NodeUid, PublicKey>)>::deserialize(d)?;
        Ok(ValidatorMap::new(public_key_set, public_keys))
    }
}

impl<NodeUid: Clone + Ord> ValidatorMap<NodeUid> {
    pub fn new(public_key_set: PublicKeySet, public_keys: BTreeMap<NodeUid, PublicKey>) -> Self {
        let num_nodes = public_keys.len();
        let node_indices: BTreeMap<NodeUid, usize> = public_keys
            .keys()
            .enumerate()
            .map(|(n, id)| (id.clone(), n))
            .collect();
        let public_key_shares = node_indices
            .iter()
            .map(|(id, idx)| (id.clone(), public_key_set.public_key_share(*idx as u64)))
            .collect();
        ValidatorMap {
            num_nodes,
            num_faulty: (num_nodes - 1) / 3,
            public_key_set,
            public_key_shares,
            node_indices,
            public_keys,
        }
    }

    /// Returns a `NetworkInfo` with the specified secrets and ID.
    pub fn into_network_info(
        self,
        our_uid: NodeUid,
        secret_key_share: SecretKeyShare,
        secret_key: SecretKey,
    ) -> NetworkInfo<NodeUid> {
        let is_validator = self.public_keys.contains_key(&our_uid);
        NetworkInfo {
            our_uid,
            is_validator,
            secret_key_share,
            secret_key,
            validator_map: self,
        }
    }

    /// ID of all nodes in the network.
    pub fn all_uids(&self) -> impl Iterator<Item = &NodeUid> {
        self.public_keys.keys()
    }

    /// The total number of nodes.
    pub fn num_nodes(&self) -> usize {
        self.num_nodes
    }

    /// The maximum number of faulty, Byzantine nodes up to which Honey Badger is guaranteed to be
    /// correct.
    pub fn num_faulty(&self) -> usize {
        self.num_faulty
    }

    /// Returns the public key set for threshold cryptography.
    pub fn public_key_set(&self) -> &PublicKeySet {
        &self.public_key_set
    }

    /// Returns the public key share if a node with that ID exists, otherwise `None`.
    pub fn public_key_share(&self, id: &NodeUid) -> Option<&PublicKeyShare> {
        self.public_key_shares.get(id)
    }

    /// Returns a map of all node IDs to their public keys.
    pub fn public_key(&self, id: &NodeUid) -> Option<&PublicKey> {
        self.public_keys.get(id)
    }

    /// Returns a map of all node IDs to their public keys.
    pub fn public_key_map(&self) -> &BTreeMap<NodeUid, PublicKey> {
        &self.public_keys
    }

    /// The index of a node in a canonical numbering of all nodes.
    pub fn node_index(&self, id: &NodeUid) -> Option<usize> {
        self.node_indices.get(id).cloned()
    }

    /// Returns the unique ID of the Honey Badger invocation.
    ///
    /// FIXME: Using the public key as the invocation ID either requires agreeing on the keys on
    /// each invocation, or makes it unsafe to reuse keys for different invocations. A better
    /// invocation ID would be one that is distributed to all nodes on each invocation and would be
    /// independent from the public key, so that reusing keys would be safer.
    pub fn invocation_id(&self) -> Vec<u8> {
        self.public_key_set.public_key().to_bytes()
    }

    /// Returns `true` if the given node takes part in the consensus itself. If not, it is only an
    /// observer.
    pub fn is_node_validator(&self, uid: &NodeUid) -> bool {
        self.public_keys.contains_key(uid)
    }
}

/// Common data shared between algorithms: the nodes' IDs and key shares.
#[derive(Debug, Clone)]
pub struct NetworkInfo<NodeUid> {
    our_uid: NodeUid,
    is_validator: bool,
    // TODO: Should this be an option? It only makes sense for validators.
    secret_key_share: SecretKeyShare,
    secret_key: SecretKey,
    validator_map: ValidatorMap<NodeUid>,
}

impl<NodeUid: Clone + Ord> NetworkInfo<NodeUid> {
    pub fn new(
        our_uid: NodeUid,
        secret_key_share: SecretKeyShare,
        public_key_set: PublicKeySet,
        secret_key: SecretKey,
        public_keys: BTreeMap<NodeUid, PublicKey>,
    ) -> Self {
        let is_validator = public_keys.contains_key(&our_uid);
        NetworkInfo {
            our_uid,
            is_validator,
            secret_key_share,
            secret_key,
            validator_map: ValidatorMap::new(public_key_set, public_keys),
        }
    }

    /// The ID of the node the algorithm runs on.
    pub fn our_uid(&self) -> &NodeUid {
        &self.our_uid
    }

    /// ID of all nodes in the network.
    pub fn all_uids(&self) -> impl Iterator<Item = &NodeUid> {
        self.validator_map.all_uids()
    }

    /// The total number of nodes.
    pub fn num_nodes(&self) -> usize {
        self.validator_map.num_nodes()
    }

    /// The maximum number of faulty, Byzantine nodes up to which Honey Badger is guaranteed to be
    /// correct.
    pub fn num_faulty(&self) -> usize {
        self.validator_map.num_faulty()
    }

    /// Returns our secret key share for threshold cryptography.
    pub fn secret_key_share(&self) -> &SecretKeyShare {
        &self.secret_key_share
    }

    /// Returns our secret key for encryption and signing.
    pub fn secret_key(&self) -> &SecretKey {
        &self.secret_key
    }

    /// Returns the public key set for threshold cryptography.
    pub fn public_key_set(&self) -> &PublicKeySet {
        self.validator_map.public_key_set()
    }

    /// Returns the public key share if a node with that ID exists, otherwise `None`.
    pub fn public_key_share(&self, id: &NodeUid) -> Option<&PublicKeyShare> {
        self.validator_map.public_key_share(id)
    }

    /// Returns a map of all node IDs to their public keys.
    pub fn public_key(&self, id: &NodeUid) -> Option<&PublicKey> {
        self.validator_map.public_key(id)
    }

    /// The index of a node in a canonical numbering of all nodes.
    pub fn node_index(&self, id: &NodeUid) -> Option<usize> {
        self.validator_map.node_index(id)
    }

    /// Returns `true` if this node takes part in the consensus itself. If not, it is only an
    /// observer.
    pub fn is_validator(&self) -> bool {
        self.is_validator
    }

    /// Returns `true` if the given node takes part in the consensus itself. If not, it is only an
    /// observer.
    pub fn is_node_validator(&self, uid: &NodeUid) -> bool {
        self.validator_map.is_node_validator(uid)
    }

    /// Returns the public validator map.
    pub fn validator_map(&self) -> &ValidatorMap<NodeUid> {
        &self.validator_map
    }

    /// Generates a map of matching `NetworkInfo`s for testing.
    pub fn generate_map<I>(uids: I) -> BTreeMap<NodeUid, NetworkInfo<NodeUid>>
    where
        I: IntoIterator<Item = NodeUid>,
    {
        use rand::{self, Rng};

        use crypto::SecretKeySet;

        let mut rng = rand::thread_rng();

        let all_uids: BTreeSet<NodeUid> = uids.into_iter().collect();
        let num_faulty = (all_uids.len() - 1) / 3;

        // Generate the keys for threshold cryptography.
        let sk_set = SecretKeySet::random(num_faulty, &mut rng);
        let pk_set = sk_set.public_keys();

        // Generate keys for individually signing and encrypting messages.
        let sec_keys: BTreeMap<_, SecretKey> =
            all_uids.iter().map(|id| (id.clone(), rng.gen())).collect();
        let pub_keys: BTreeMap<_, PublicKey> = sec_keys
            .iter()
            .map(|(id, sk)| (id.clone(), sk.public_key()))
            .collect();

        // Create the corresponding `NetworkInfo` for each node.
        let create_netinfo = |(i, uid): (usize, NodeUid)| {
            let netinfo = NetworkInfo::new(
                uid.clone(),
                sk_set.secret_key_share(i as u64),
                pk_set.clone(),
                sec_keys[&uid].clone(),
                pub_keys.clone(),
            );
            (uid, netinfo)
        };
        all_uids
            .into_iter()
            .enumerate()
            .map(create_netinfo)
            .collect()
    }
}
