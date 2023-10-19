--------------------- MODULE LNContracsUsingBitcoinTransactions ------------

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
    commitment_txs,         \* Commitment txs held by each party. Not yet broadcast.
    breach_remedy_txs       \* BR txs held by each party. Not yet broadcast.

-----------------------------------------------------------------------------

SeqToSet(s) == {s[i] : i \in DOMAIN s}

-----------------------------------------------------------------------------

vars == <<chain_height, transactions, mempool, published,
           commitment_txs, breach_remedy_txs>>

Init ==
    /\ transactions = [id \in TXID |-> [inputs |-> <<>>, outputs |-> <<>>]]
    /\ commitment_txs = [p \in PARTY |-> {} ]
    /\ breach_remedy_txs = [p \in PARTY |-> {} ]
    /\ chain_height = 0
    /\ mempool = {}
    /\ published = [id \in TXID |-> NoSpendHeight]
    
TypeOK ==
    /\ transactions \in [TXID -> [inputs: Seq(Input), outputs: Seq(Output)]]
    /\ commitment_txs \in [PARTY -> SUBSET TXID ]
    /\ breach_remedy_txs \in [PARTY -> SUBSET TXID ]
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

ChoosePartyKey(party) ==
    CHOOSE k \in Keys: k[1] = party

AllCommitmentsTxids ==
    UNION {commitment_txs[p]: p \in PARTY}

AllBreachRemedyTxids ==
    UNION {breach_remedy_txs[p]: p \in PARTY}


-----------------------------------------------------------------------------

(***************************************************************************)
(* Confirm a transaction in mempool.  This publishes the transaction.      *)
(*                                                                         *)
(* We need to add a function like IsOutputSpent(o) which checks if there   *)
(* is any transaction in published with o as input.                        *)
(***************************************************************************)
ConfirmTx(id) ==
    /\ ConfirmMempoolTx(id)
    /\ UNCHANGED <<commitment_txs, breach_remedy_txs>>


(***************************************************************************)
(* We generate simple p2wkh transactions as inputs for funding             *)
(* transactions                                                            *)
(***************************************************************************)
CreateInputsForFundingTx(id, party, amount) ==
    /\ AddP2WKHCoinbaseToMempool(id, <<ChoosePartyKey(party)>>, amount)
    /\ UNCHANGED <<commitment_txs, breach_remedy_txs>>

(***************************************************************************
Create funding transaction that is signed by both parties for a channel.
 ***************************************************************************)
CreateConfirmedFundingTxByParty(id, channel, amount) ==
    \E o \in UnspentOutputs, p \in channel:
        \* transaction with id not created yet
        /\ id \notin mempool
        /\ published[id] = NoSpendHeight
        /\ id \notin AllCommitmentsTxids
        /\ id \notin AllBreachRemedyTxids
        /\ OutputOwnedByParty(o, p)
        /\ chain_height' = chain_height + 1                 \* Each tx is in it's own block
        /\ LET fundingTx == CreateMultisigTx(o, id, ChooseOutputKeys("multisig"), amount)
           IN
            /\ transactions' = [transactions EXCEPT ![id] = fundingTx]
            /\ published' = [published EXCEPT ![id] = chain_height']
        /\ UNCHANGED <<commitment_txs, breach_remedy_txs, mempool>>

(****************************************************************************
Create a commitment transaction for a party, sign it appropriately and
send it to the other party.

Use a published funding transaction and its output as an input to the
commitment tx.
****************************************************************************)
\*CreateCommitmentTxs(aid, bid) ==
\*    \E ftxid \in DOMAIN published:
\*        /\ published[ftxid] # NoSpendHeight
\*        /\ published[ftxid] < chain_height
\*        /\ published[ftxid].outputs.type = "multisig"
    
-----------------------------------------------------------------------------
Next ==
    \/ \E id \in TXID, party \in PARTY, amount \in AMOUNT:
        \/ CreateInputsForFundingTx(id, party, amount)
    \/ \E id \in TXID: ConfirmTx(id)
    \/ \E id \in TXID, channel \in CHANNEL_PARTY, amount \in AMOUNT:
        \/ CreateConfirmedFundingTxByParty(id, channel, amount)
\*    \/ \E id \in TXID: ConfirmTx(id)
\*    \/ \E <<aid, bid>> \in TXID \X TXID: CreateCommitmentTxs(aid, bid)

Spec == 
    /\ Init
    /\ [][Next]_<<vars>>

=============================================================================
