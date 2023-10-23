--------------------- MODULE LNContractsUsingBitcoinTransactions ------------

(***************************************************************************)
(* This spec captures the behaviour of commitment transactions on the two  *)
(* sides of a Lightning channel.                                           *)
(*                                                                         *)
(* We model the various kinds of outputs a commitment transactions will    *)
(* have over its lifetime.                                                 *)
(*                                                                         *)
(* The state of the commitment transaction changes in reponse to the       *)
(* various actions like supersede, publish, etc are taken by parties.      *)
(*                                                                         *)
(* We also do not deal with the communication protocol between nodes for   *)
(* creating and updating commitment transactions.  This spec will only     *)
(* focus on the various commitment transaction and their lifecycle in      *)
(* response to interaction between parties and the blockchain.             *)
(*                                                                         *)
(* We ignore the details of how transactions are signed and just mark      *)
(* transactions as signed.  This lets us focus on the specifying the       *)
(* behaviour of the commitment transactions without dealing with lower     *)
(* level complexities.                                                     *)
(*                                                                         *)
(* The model defines the intial balance from alice to bob.  TLA+ will      *)
(* handle situations where channels are balanced and when all the balance  *)
(* is on the other side.                                                   *)
(*                                                                         *)
(* TODO: Add actions for closing channels.  Currenly we only have support  *)
(* for breach tx and the corresponding breach remedy txs.                  *)
(*                                                                         *)
(* TODO: Add HTLCs.                                                        *)
(***************************************************************************)

EXTENDS Integers,
        TLC,
        Sequences,
        FiniteSets,
        BitcoinTransactions

CONSTANTS
    INITIAL_BALANCE,    \* Initial balances for alice and bob
    CHANNEL_PARTY       \* Channel between parties
    
VARIABLES
    funding_txs,             \* The TXID for the channel funding txs
    commitment_txs,         \* Commitment txs held by each party. Not yet broadcast.
    breach_remedy_txs,      \* BR txs held by each party. Not yet broadcast.
    funding_input_txs       \* Transactions spent by funding transactions

-----------------------------------------------------------------------------

SeqToSet(s) == {s[i] : i \in DOMAIN s}

-----------------------------------------------------------------------------

vars == <<chain_height, transactions, mempool, published,
           commitment_txs, breach_remedy_txs, funding_txs,
            funding_input_txs>>

Init ==
    /\ transactions = [id \in TXID |-> [inputs |-> <<>>, outputs |-> <<>>]]
    /\ funding_txs = [channel \in CHANNEL_PARTY |-> NoTxid]
    /\ funding_input_txs = [channel \in CHANNEL_PARTY |-> NoTxid]
    /\ commitment_txs = [channel \in CHANNEL_PARTY |-> [p \in channel |-> NoTxid] ]
    /\ breach_remedy_txs = [channel \in CHANNEL_PARTY |-> [p \in channel |-> NoTxid] ]
    /\ chain_height = 0
    /\ mempool = {}
    /\ published = [id \in TXID |-> NoSpendHeight]
    
TypeOK ==
    /\ transactions \in [TXID -> [inputs: Seq(Input), outputs: Seq(Output)]]
    /\ funding_txs \in [CHANNEL_PARTY -> TXID \cup {NoTxid} ]
    /\ funding_input_txs \in [CHANNEL_PARTY -> TXID \cup {NoTxid} ]
    /\ commitment_txs \in [CHANNEL_PARTY -> [PARTY -> TXID \cup {NoTxid}] ]
    /\ breach_remedy_txs \in [CHANNEL_PARTY -> [PARTY -> TXID \cup {NoTxid}] ]
    /\ mempool \in SUBSET TXID
    /\ published \in [TXID -> Int]
-----------------------------------------------------------------------------

(***************************************************************************)
(* Choose keys for parties that have a channel.                            *)
(*                                                                         *)
(* The keys should have the same sequence number.  This becomes important  *)
(* when parties create commitment transactions.                            *)
(***************************************************************************)
ChooseChannelKeys ==
    CHOOSE <<j, k>> \in Keys \X Keys:
        /\ {j[1], k[1]} \in CHANNEL_PARTY       \* Choose parties that have a channel
        /\ j[2] = k[2]                          \* Choose keys with same index

ChannelKeys(channel) == SetToSeq({<<p, 1>>: p \in channel})

ChoosePartyKey(party) ==
    CHOOSE k \in Keys: k[1] = party

OtherParty(channel, party) ==
    CHOOSE p \in channel: p # party

AllCommitmentsTxids ==
    {commitment_txs[cp[1]][cp[2]]: 
        cp \in {<<channel_party, party>> \in CHANNEL_PARTY \X PARTY: party \in channel_party}}


AllBreachRemedyTxids ==
    {breach_remedy_txs[cp[1]][cp[2]]: 
        cp \in {<<channel_party, party>> \in CHANNEL_PARTY \X PARTY: party \in channel_party}}

(***************************************************************************)
(* TXID id has not been used yet.                                          *)
(*                                                                         *)
(* TODO: We might need to rethink how we track txids, but for now, this is *)
(* the solution.                                                           *)
(***************************************************************************)
IsUnused(id) ==
    /\ id \notin mempool
    /\ published[id] = NoSpendHeight
    /\ id \notin AllCommitmentsTxids
    /\ id \notin AllBreachRemedyTxids
    /\ id \notin {funding_txs[t]: t \in CHANNEL_PARTY}
    
-----------------------------------------------------------------------------

(***************************************************************************)
(* Confirm a transaction in mempool.  This publishes the transaction.      *)
(*                                                                         *)
(* We need to add a function like IsOutputSpent(o) which checks if there   *)
(* is any transaction in published with o as input.                        *)
(***************************************************************************)
ConfirmTx(id) ==
    /\ ConfirmMempoolTx(id)
    /\ UNCHANGED <<commitment_txs, breach_remedy_txs, funding_txs,
                    funding_input_txs>>


(***************************************************************************)
(* We generate simple p2wkh transactions as inputs for funding             *)
(* transactions                                                            *)
(*                                                                         *)
(* Outputs both have INITIAL_BALANCE * 2 so that later we can have         *)
(* bi-directional channel with INITIAL_BALANCE                             *)
(***************************************************************************)
CreateInputsForFundingTx(id, channel) ==
    /\ funding_txs[channel] = NoTxid        \* No funding tx for channel exists
    /\ funding_input_txs[channel] = NoTxid
    /\ \E party \in channel:
        /\ LET tx == [inputs |-> <<>>,
                     outputs |-> <<CreateP2WKHOutput(<<ChoosePartyKey(party)>>,
                                    INITIAL_BALANCE * 2)>>]
           IN
            /\ transactions' = [transactions EXCEPT ![id] = tx]
            /\ funding_input_txs' = [funding_input_txs EXCEPT ![channel] = id]
            /\ AddTxidToMempool(id)
    /\ UNCHANGED <<commitment_txs, breach_remedy_txs, funding_txs>>

(***************************************************************************)
(* Create funding transaction.  The funding tx is not locked at this       *)
(* point.                                                                  *)
(*                                                                         *)
(* Once a commitment tx is signed then we can send this funding tx to the  *)
(* mempool.                                                                *)
(*                                                                         *)
(* Create a funding tx only if no funding tx exists for the channel        *)
(***************************************************************************)
CreateFundingTxByParty(id, channel) ==
    \E o \in UnspentOutputs, p \in channel:
        \* transaction with id not created yet
        /\ IsUnused(id)
        /\ funding_txs[channel] = NoTxid    \* No funding tx exists for the channel
        /\ OutputOwnedByParty(o, p)
        /\ LET  fundingTx == CreateUnsignedMultisigTx(o, ChannelKeys(channel), INITIAL_BALANCE)
           IN
            /\ transactions' = [transactions EXCEPT ![id] = fundingTx]
            /\ funding_txs' = [funding_txs EXCEPT ![channel] = id]
        /\ UNCHANGED <<commitment_txs, breach_remedy_txs,
                        chain_height, published, mempool, funding_input_txs>>


CreateCommitmentTxInput(ftxid, ftx) ==
    <<[txid |-> ftxid,
        index |-> ftx.outputs[1].index,         \* Assume we only have one output in ftx
        sighash_flag |-> "all",
        signed_by |-> ftx.outputs[1].keys,
        hash_preimage |-> NoHash]>>

CreateCommitmentTxOutputs(channel, party, ftxid, ftx) ==
    IF party = ftx.outputs[1].keys[1][1]
    THEN
        \* No output for other party as only one party funded the channel
        <<CreateP2WKHWithCSVOutput(<<ftx.outputs[1].keys[1]>>,
                                    ftx.outputs[1].amount)>>
    ELSE <<>>

(***************************************************************************)
(* Create a commitment tx for for a channel parties.                       *)
(***************************************************************************)
CreateCommitmentTx(txid, channel, party) ==
    \* txid is not used
    /\ IsUnused(txid)
    \* Funding tx for channel exists
    /\ funding_txs[channel] # NoTxid
    \* Commitment tx for channel and party doesn't exist
    /\ commitment_txs[channel][party] = NoTxid
    \* Create the commitment tx for party paying back to funder with CSV
    /\ LET  ftxid == funding_txs[channel]
            ftx == transactions[ftxid]
            ftx_input == transactions[ftx.inputs[1].txid]
            \* Create commitment tx, that spends ftx and creates outputs for party and other party
            \* Use amounts based on party = funding input key holder
            tx == [inputs |-> CreateCommitmentTxInput(ftxid, ftx),
                outputs |-> CreateCommitmentTxOutputs(channel, party, ftxid, ftx)]
       IN
        /\ commitment_txs' = [commitment_txs EXCEPT ![channel][party] = txid]
        /\ transactions' = [transactions EXCEPT ![txid] = tx]
    /\ UNCHANGED <<breach_remedy_txs, funding_txs,
                    chain_height, published, mempool, funding_input_txs>>

(***************************************************************************)
(* Add funding tx to mempool once commitment transactions have been signed *)
(* and shared.                                                             *)
(***************************************************************************)
AddFundingTxToMempool(txid, channel) ==
    LET
        funding_txid == funding_txs[channel]
    IN
    /\ funding_txid # NoTxid          \* A funding tx exists
    /\ \A p \in channel: 
        \* There is a commitment tx for both parties    
        /\ commitment_txs[channel][p] # NoTxid
        \* both commitment tx spending the funding tx
        /\ transactions[commitment_txs[channel][p]].inputs[1].txid = funding_txid
    /\ mempool' = mempool \cup {funding_txid}
    /\ UNCHANGED <<commitment_txs, breach_remedy_txs,
                    chain_height, published, funding_txs, transactions,
                    funding_input_txs>>
-----------------------------------------------------------------------------
Next ==
    \/ \E id \in TXID, channel \in CHANNEL_PARTY:
        \/ CreateInputsForFundingTx(id, channel)
    \/ \E id \in TXID: ConfirmTx(id)
    \/ \E id \in TXID, channel \in CHANNEL_PARTY:
        \/ CreateFundingTxByParty(id, channel)
        \/ AddFundingTxToMempool(id, channel)
    \/ \E channel \in CHANNEL_PARTY:
            \E <<txid, party>> \in TXID \X channel:
               CreateCommitmentTx(txid, channel, party)

Spec == 
    /\ Init
    /\ [][Next]_<<vars>>

=============================================================================
