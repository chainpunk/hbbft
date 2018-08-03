use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;
use std::sync::Arc;

use bincode;
use crypto::Ciphertext;
use itertools::Itertools;
use rand::Rand;
use serde::{Deserialize, Serialize};

use super::{Batch, Error, ErrorKind, HoneyBadgerBuilder, Message, MessageContent, Result};
use common_subset::{self, CommonSubset};
use fault_log::{FaultKind, FaultLog};
use messaging::{self, DistAlgorithm, NetworkInfo};
use threshold_decryption::{self as td, ThresholdDecryption};
use traits::{Contribution, NodeUidT};

/// The status of an encrypted contribution.
#[derive(Debug)]
enum DecryptionState<N> {
    /// Decryption is still ongoing; we are waiting for decryption shares and/or ciphertext.
    Ongoing(Box<ThresholdDecryption<N>>),
    /// Decryption is complete. This contains the plaintext.
    Complete(Vec<u8>),
}

impl<N> DecryptionState<N>
where
    N: NodeUidT + Rand,
{
    fn new(netinfo: Arc<NetworkInfo<N>>) -> Self {
        DecryptionState::Ongoing(Box::new(ThresholdDecryption::new(netinfo)))
    }

    fn handle_message(&mut self, sender_id: &N, msg: td::Message) -> td::Result<td::Step<N>> {
        match self {
            DecryptionState::Ongoing(ref mut td) => td.handle_message(sender_id, msg),
            DecryptionState::Complete(_) => Ok(td::Step::default()),
        }
    }

    fn input(&mut self, ciphertext: Ciphertext) -> td::Result<td::Step<N>> {
        match self {
            DecryptionState::Ongoing(ref mut td) => td.input(ciphertext),
            DecryptionState::Complete(_) => Ok(td::Step::default()),
        }
    }

    fn plaintext(&self) -> Option<&[u8]> {
        match self {
            DecryptionState::Ongoing(_) => None,
            DecryptionState::Complete(ref plaintext) => Some(&plaintext[..]),
        }
    }
}

/// The status of the subset algorithm.
#[derive(Debug)]
enum SubsetState<N: Rand> {
    /// The algorithm is ongoing: the set of accepted contributions is still undecided.
    Ongoing(CommonSubset<N>),
    /// The algorithm is complete. This contains the set of accepted proposers.
    Complete(BTreeSet<N>),
}

/// The sub-algorithms and their intermediate results for a single epoch.
#[derive(Debug)]
pub struct EpochState<C, N: Rand> {
    /// Our epoch number.
    epoch: u64,
    /// Shared network data.
    netinfo: Arc<NetworkInfo<N>>,
    /// The status of the subset algorithm.
    subset: SubsetState<N>,
    /// The status of threshold decryption, by proposer.
    decryption: BTreeMap<N, DecryptionState<N>>,
    _phantom: PhantomData<C>,
}

impl<C, N> EpochState<C, N>
where
    C: Contribution + Serialize + for<'r> Deserialize<'r>,
    N: NodeUidT + Rand,
{
    fn new(netinfo: Arc<NetworkInfo<N>>, epoch: u64) -> Result<Self> {
        let cs = CommonSubset::new(netinfo.clone(), epoch).map_err(ErrorKind::CreateCommonSubset)?;
        Ok(EpochState {
            epoch,
            netinfo,
            subset: SubsetState::Ongoing(cs),
            decryption: BTreeMap::default(),
            _phantom: PhantomData,
        })
    }

    fn propose(&mut self, ciphertext: &Ciphertext) -> Result<Step<C, N>> {
        let ser_ct = bincode::serialize(ciphertext).map_err(|err| ErrorKind::ProposeBincode(*err))?;
        let cs_step = match self.subset {
            SubsetState::Ongoing(ref mut cs) => cs.input(ser_ct),
            SubsetState::Complete(_) => return Ok(Step::default()),
        }.map_err(ErrorKind::InputCommonSubset)?;
        self.process_subset(cs_step)
    }

    fn received_proposals(&self) -> usize {
        match self.subset {
            SubsetState::Ongoing(ref cs) => cs.received_proposals(),
            SubsetState::Complete(_) => self.netinfo.num_nodes(),
        }
    }

    fn handle_message_content(
        &mut self,
        sender_id: &N,
        content: MessageContent<N>,
    ) -> Result<Step<C, N>> {
        match content {
            MessageContent::CommonSubset(cs_msg) => self.handle_subset_message(sender_id, cs_msg),
            MessageContent::DecryptionShare { proposer_id, share } => {
                self.handle_decryption_message(sender_id, proposer_id, share)
            }
        }
    }

    /// Handles a message for the common subset sub-algorithm.
    fn handle_subset_message(
        &mut self,
        sender_id: &N,
        message: common_subset::Message<N>,
    ) -> Result<Step<C, N>> {
        let cs_step = match self.subset {
            SubsetState::Ongoing(ref mut cs) => cs.handle_message(sender_id, message),
            SubsetState::Complete(_) => return Ok(Step::default()),
        }.map_err(ErrorKind::HandleCommonSubsetMessage)?;
        self.process_subset(cs_step)
    }

    /// Handles decryption shares sent by `HoneyBadger` instances.
    fn handle_decryption_message(
        &mut self,
        sender_id: &N,
        proposer_id: N,
        share: td::Message,
    ) -> Result<Step<C, N>> {
        let td_step = match self.decryption.entry(proposer_id.clone()) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(DecryptionState::new(self.netinfo.clone())),
        }.handle_message(sender_id, share)
            .map_err(ErrorKind::ThresholdDecryption)?;
        self.process_decryption(proposer_id, td_step)
    }

    /// Checks whether the subset has output, and if it does, sends out our decryption
    /// shares.
    fn process_subset(&mut self, cs_step: common_subset::Step<N>) -> Result<Step<C, N>> {
        let mut step = Step::default();
        let mut cs_outputs = step.extend_with(cs_step, |cs_msg| {
            MessageContent::CommonSubset(cs_msg).with_epoch(self.epoch)
        });
        if let Some(cs_output) = cs_outputs.pop_front() {
            self.subset = SubsetState::Complete(cs_output.keys().cloned().collect());
            step.extend(self.send_decryption_shares(cs_output)?);
        }
        if !cs_outputs.is_empty() {
            error!("Multiple outputs from a single Common Subset instance.");
        }
        Ok(step)
    }

    /// Processes a Threshold Decryption step.
    fn process_decryption(&mut self, proposer_id: N, td_step: td::Step<N>) -> Result<Step<C, N>> {
        let mut step = Step::default();
        let opt_output = step.extend_with(td_step, |share| {
            MessageContent::DecryptionShare {
                proposer_id: proposer_id.clone(),
                share,
            }.with_epoch(self.epoch)
        });
        if let Some(output) = opt_output.into_iter().next() {
            self.decryption
                .insert(proposer_id, DecryptionState::Complete(output));
        }
        Ok(step)
    }

    fn send_decryption_shares(&mut self, cs_output: BTreeMap<N, Vec<u8>>) -> Result<Step<C, N>> {
        let mut step = Step::default();
        for (proposer_id, v) in cs_output {
            // TODO: Input into ThresholdDecryption. Check errors!
            let ciphertext: Ciphertext = match bincode::deserialize(&v) {
                Ok(ciphertext) => ciphertext,
                Err(err) => {
                    warn!(
                        "Cannot deserialize ciphertext from {:?}: {:?}",
                        proposer_id, err
                    );
                    let fault_kind = FaultKind::InvalidCiphertext;
                    step.fault_log.append(proposer_id, fault_kind);
                    continue;
                }
            };
            let netinfo = self.netinfo.clone();
            let td_step = match self
                .decryption
                .entry(proposer_id.clone())
                .or_insert_with(|| DecryptionState::new(netinfo))
                .input(ciphertext)
            {
                Ok(td_step) => td_step,
                Err(td::Error::InvalidCiphertext(_)) => {
                    warn!("Invalid ciphertext from {:?}", proposer_id);
                    let fault_kind = FaultKind::ShareDecryptionFailed;
                    step.fault_log.append(proposer_id.clone(), fault_kind);
                    continue;
                }
                Err(err) => return Err(ErrorKind::ThresholdDecryption(err).into()),
            };
            step.extend(self.process_decryption(proposer_id, td_step)?);
        }
        Ok(step)
    }

    /// When contributions of transactions have been decrypted for all valid proposers in this
    /// epoch, moves those contributions into a batch, outputs the batch and updates the epoch.
    fn try_output_batch(&self) -> Option<(Batch<C, N>, FaultLog<N>)> {
        let proposer_ids = match self.subset {
            SubsetState::Ongoing(_) => return None, // The set is not yet decided.
            SubsetState::Complete(ref proposer_ids) => proposer_ids,
        };
        let plaintexts: BTreeMap<N, &[u8]> = self
            .decryption
            .iter()
            .flat_map(|(id, dec_state)| dec_state.plaintext().map(|pt| (id.clone(), pt)))
            .collect();
        if !proposer_ids.iter().eq(plaintexts.keys()) {
            return None; // Decryption of contributions is still ongoing.
        }

        let mut fault_log = FaultLog::default();

        // Deserialize the output.
        let contributions: BTreeMap<N, C> = plaintexts
            .into_iter()
            .flat_map(|(id, plaintext)| {
                match bincode::deserialize::<C>(plaintext) {
                    Ok(contrib) => Some((id, contrib)),
                    Err(_) => {
                        // If deserialization fails, the proposer of that item is faulty. Ignore it.
                        fault_log.append(id, FaultKind::BatchDeserializationFailed);
                        None
                    }
                }
            })
            .collect();
        let batch = Batch {
            epoch: self.epoch,
            contributions,
        };
        debug!(
            "{:?} Epoch {} output {:?}",
            self.netinfo.our_uid(),
            self.epoch,
            batch.contributions.keys().collect::<Vec<_>>()
        );
        Some((batch, fault_log))
    }
}

/// An instance of the Honey Badger Byzantine fault tolerant consensus algorithm.
#[derive(Debug)]
pub struct HoneyBadger<C, N: Rand> {
    /// Shared network data.
    pub(super) netinfo: Arc<NetworkInfo<N>>,
    /// The earliest epoch from which we have not yet received output.
    pub(super) epoch: u64,
    /// Whether we have already submitted a proposal for the current epoch.
    pub(super) has_input: bool,
    /// The subalgorithms for ongoing epochs.
    pub(super) epochs: BTreeMap<u64, EpochState<C, N>>,
    /// The maximum number of `CommonSubset` instances that we run simultaneously.
    pub(super) max_future_epochs: u64,
    /// Messages for future epochs that couldn't be handled yet.
    pub(super) incoming_queue: BTreeMap<u64, Vec<(N, MessageContent<N>)>>,
}

pub type Step<C, N> = messaging::Step<HoneyBadger<C, N>>;

impl<C, N> DistAlgorithm for HoneyBadger<C, N>
where
    C: Contribution + Serialize + for<'r> Deserialize<'r>,
    N: NodeUidT + Rand,
{
    type NodeUid = N;
    type Input = C;
    type Output = Batch<C, N>;
    type Message = Message<N>;
    type Error = Error;

    fn input(&mut self, input: Self::Input) -> Result<Step<C, N>> {
        self.propose(&input)
    }

    fn handle_message(&mut self, sender_id: &N, message: Self::Message) -> Result<Step<C, N>> {
        if !self.netinfo.is_node_validator(sender_id) {
            return Err(ErrorKind::UnknownSender.into());
        }
        let Message { epoch, content } = message;
        if epoch > self.epoch + self.max_future_epochs {
            // Postpone handling this message.
            self.incoming_queue
                .entry(epoch)
                .or_insert_with(Vec::new)
                .push((sender_id.clone(), content));
        } else if epoch == self.epoch {
            return self.handle_message_content(sender_id, epoch, content);
        } // And ignore all messages from past epochs.
        Ok(Step::default())
    }

    fn terminated(&self) -> bool {
        false
    }

    fn our_id(&self) -> &N {
        self.netinfo.our_uid()
    }
}

impl<C, N> HoneyBadger<C, N>
where
    C: Contribution + Serialize + for<'r> Deserialize<'r>,
    N: NodeUidT + Rand,
{
    /// Returns a new `HoneyBadgerBuilder` configured to use the node IDs and cryptographic keys
    /// specified by `netinfo`.
    pub fn builder(netinfo: Arc<NetworkInfo<N>>) -> HoneyBadgerBuilder<C, N> {
        HoneyBadgerBuilder::new(netinfo)
    }

    /// Proposes a new item in the current epoch.
    pub fn propose(&mut self, proposal: &C) -> Result<Step<C, N>> {
        if !self.netinfo.is_validator() {
            return Ok(Step::default());
        }
        self.has_input = true;
        let epoch = self.epoch;
        let ser_prop =
            bincode::serialize(&proposal).map_err(|err| ErrorKind::ProposeBincode(*err))?;
        let ciphertext = self.netinfo.public_key_set().public_key().encrypt(ser_prop);
        let mut step = match self.epochs.entry(epoch) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(EpochState::new(self.netinfo.clone(), epoch)?),
        }.propose(&ciphertext)?;
        step.extend(self.try_output_batches()?);
        Ok(step)
    }

    /// Returns `true` if input for the current epoch has already been provided.
    pub fn has_input(&self) -> bool {
        !self.netinfo.is_validator() || self.has_input
    }

    /// Returns the number of validators from which we have already received a proposal for the
    /// current epoch.
    pub(crate) fn received_proposals(&self) -> usize {
        self.epochs
            .get(&self.epoch)
            .map_or(0, EpochState::received_proposals)
    }

    /// Handles a message for the given epoch.
    fn handle_message_content(
        &mut self,
        sender_id: &N,
        epoch: u64,
        content: MessageContent<N>,
    ) -> Result<Step<C, N>> {
        let mut step = match self.epochs.entry(epoch) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                entry.insert(EpochState::new(self.netinfo.clone(), self.epoch)?)
            }
        }.handle_message_content(sender_id, content)?;
        step.extend(self.try_output_batches()?);
        Ok(step)
    }

    /// Increments the epoch number and clears any state that is local to the finished epoch.
    fn update_epoch(&mut self) -> Result<Step<C, N>> {
        // Clear the state of the old epoch.
        self.epochs.remove(&self.epoch);
        self.epoch += 1;
        self.has_input = false;
        let max_epoch = self.epoch + self.max_future_epochs;
        let mut step = Step::default();
        // TODO: Once stable, use `Iterator::flatten`.
        for (sender_id, content) in
            Itertools::flatten(self.incoming_queue.remove(&max_epoch).into_iter())
        {
            step.extend(self.handle_message_content(&sender_id, max_epoch, content)?);
        }
        // Handle any decryption shares received for the new epoch.
        step.extend(self.try_output_batches()?);
        Ok(step)
    }

    /// Tries to decrypt contributions from all proposers and output those in a batch.
    fn try_output_batches(&mut self) -> Result<Step<C, N>> {
        let mut step = Step::default();
        while let Some((batch, fault_log)) = self
            .epochs
            .get(&self.epoch)
            .and_then(EpochState::try_output_batch)
        {
            // Queue the output and advance the epoch.
            step.output.push_back(batch);
            step.fault_log.extend(fault_log);
            step.extend(self.update_epoch()?);
        }
        Ok(step)
    }
}
