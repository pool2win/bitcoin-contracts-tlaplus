----------------------------- MODULE LNContracts ---------------------------

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
        FiniteSets

CONSTANTS
    CSV,             \* The csv value to use in contracts
    InitialBalance   \* Initial balances for alice and bob

-----------------------------------------------------------------------------

SeqToSet(s) == {s[i] : i \in DOMAIN s}

-----------------------------------------------------------------------------

(***************************************************************************)
(* Current channel contracts only ever have two parties                    *)
(***************************************************************************)
Party == {"alice", "bob"}

(***************************************************************************)
(* For the first revocation we only need two keys per party                *)
(***************************************************************************)
NumKey == 2

(***************************************************************************)
(* Set of all keys                                                         *)
(***************************************************************************)
Key == {<<p, k>>: p \in Party, k \in 0..NumKey}

(***************************************************************************)
(* Value to capture missing CSV in output                                  *)
(***************************************************************************)
NoCSV == CHOOSE c : c \notin 0..CSV

(***************************************************************************)
(* Abstract out all outputs as meant to be spent by a party, is it signed  *)
(* by party and other party.                                               *)
(***************************************************************************)
Output == [party: Party,
           type: {"multisig", "p2wkh"},
           csv: {CSV} \cup {NoCSV},
           amount: 0..InitialBalance*2] \* All the balance can be on one side

(***************************************************************************)
(* Multisig with no csv encumberance                                       *)
(***************************************************************************)
CreateMultisigOutput(party, amount) ==
    [type |-> "multisig",
     party |-> party,
     csv |-> NoCSV,
     amount |-> amount]

CreateRSMCOutput(party, amount) ==
    [type |-> "multisig",
     party |-> party,
     csv |-> CSV,
     amount |-> amount]

CreatePKOutput(party, amount) ==
    [type |-> "p2wkh",
     party |-> party,
     csv |-> NoCSV,
     amount |-> amount]

NoSpendHeight == -1

(***************************************************************************)
(* In contrast to txids, we simlpy use the party, index tuple to find the  *)
(* tx and the vout to get the output pointed to by the input               *)
(***************************************************************************)
Input == [party: Party, index: Int, vout: Int]

(***************************************************************************)
(* Transaction record.                                                     *)
(***************************************************************************)
Tx == [party: Party,
      index: Int,
      height: Int,
      inputs: Seq(Input),
      outputs: Seq(Output),
      party_signed: BOOLEAN,
      other_party_signed: BOOLEAN]

-----------------------------------------------------------------------------

VARIABLES
    cts,            \* Commitment tx for all parties
    brs,            \* Breach remedy transactions for all parties
    mempool,        \* The CT txs that have been broadcasted.
    published,      \* The CT that has been included in a block and confirmed.
    index,
    chain_height

vars == <<cts, brs, mempool, published, chain_height, index>>

(***************************************************************************)
(* Helper function to get other party                                      *)
(***************************************************************************)
OtherParty(party) == CHOOSE p \in Party: p # party

(***************************************************************************)
(* The channel funding transaction.  All commitment txs spend from the     *)
(* output of this tx.                                                      *)
(***************************************************************************)
FundingTx ==
    [party |-> "alice",                     \* Only alice is funding
     index |-> 1,
     height |-> 1,
     inputs |-> <<>>,                       \* FT inputs do not matter
     outputs |-> <<CreateMultisigOutput("alice", InitialBalance)>>,
     party_signed |-> TRUE,
     other_party_signed |-> TRUE
    ]


(***************************************************************************)
(* Create a commitment transaction given the party, index and key to use.  *)
(*                                                                         *)
(* Other party hands this CT to this party, therefore it is signed by      *)
(* other party.                                                            *)
(***************************************************************************)
CreateCT(party, i, key_num, amount, other_amount) ==
        [party |-> party,
         index |-> i,
         height |-> NoSpendHeight,
         \* Input for CT is the FT multisig output (1, 1)
         inputs |-> <<[party |-> "alice", index |-> 1, vout |-> 1]>>,
         outputs |-> <<CreateRSMCOutput(party, amount),
                      CreatePKOutput(OtherParty(party), other_amount)>>,
        party_signed |-> FALSE,
        other_party_signed |-> TRUE]

(***************************************************************************)
(* Breach remedy transactions are handled as presigned transactions        *)
(* instead of by passing private keys around.  This is different from the  *)
(* Poon-Dryja LN paper.                                                    *)
(*                                                                         *)
(* The party creates this tx, signs it and sends it to the other party.    *)
(***************************************************************************)
CreateBR(party, i, amount) ==
        [party |-> party,
         index |-> i,
         height |-> NoSpendHeight,
         \* BR spend the RSMC output from the corresponding index CT.
         inputs |-> <<[party |-> OtherParty(party), index |-> i, vout |-> 1]>>,
         \* Spending BR output will give the balance to party
         outputs |-> <<CreatePKOutput(party, amount)>>,
         party_signed |-> TRUE,
         \* The other party presigns the BR so that this party can spend it
         \* TODO: switch to exchanging private keys for the BR instead
         other_party_signed |-> TRUE]

Init ==
    \* Balanced channel to start with
    /\ cts = {CreateCT("alice", 2, 0, InitialBalance, 0),
              CreateCT("bob", 2, 0, 0, InitialBalance)}
    /\ brs = {CreateBR("bob", 2, InitialBalance),
              CreateBR("alice", 2, 0)}      \* Bob did not add funds
    /\ mempool = {}
    /\ published = {FundingTx}
    /\ index = 3
    /\ chain_height = 1 \* The genesis block is the FT

TypeInvariant ==
    /\ index \in Int
    /\ cts \in SUBSET Tx
    /\ brs \in SUBSET Tx
    /\ mempool \in SUBSET Tx
    /\ published \in SUBSET Tx

-----------------------------------------------------------------------------

LastCT(party) ==
    CHOOSE ct \in cts: \A y \in cts: 
        ct.party = party /\ ct.index >= y.index

MaxIndex(party_cts) ==
    (LastCT(party_cts)).index

AnyCT == (CHOOSE ct \in cts: TRUE)

(***************************************************************************)
(* Create commitment transaction as well as the corresponding beach remedy *)
(* txs.                                                                    *)
(*                                                                         *)
(* Breach remedy transactions are pre-signed transactions instead of they  *)
(* private key being sent over to the other party.                         *)
(*                                                                         *)
(* delta is the balance going from alice to bob.  We allow negative        *)
(* balances to enable payments in other other direction.                   *)
(*                                                                         *)
(* Parties are free to keep creating CT even if FT is spent.  They will    *)
(* not be usable, but the protocol does not disallow this.                 *)
(***************************************************************************)
SupersedeCommitmentTx(delta) ==
    /\
        LET
            key_index == 1 \* TODO: manage key numbers
            last_alice_ct == LastCT("alice")
            last_bob_ct == LastCT("bob")
        IN
            \* Create CTs till channel is not closed
            /\ published = {FundingTx}
            /\ last_alice_ct.outputs[1].amount - delta > 0
            /\ last_alice_ct.outputs[2].amount + delta <= InitialBalance
            /\ cts' = cts \cup
                    {CreateCT("alice", index, key_index,
                        last_alice_ct.outputs[1].amount - delta,
                        last_alice_ct.outputs[2].amount + delta),
                     CreateCT("bob", index, key_index,
                        last_bob_ct.outputs[1].amount + delta,
                        last_bob_ct.outputs[2].amount - delta)}
            \* Alice's gets a BR it can immediately spend when corresponding
            \* CT is spen, and vice versa
            /\ brs' = brs \cup
                        {CreateBR("bob", index, last_alice_ct.outputs[1].amount),
                         CreateBR("alice", index, last_bob_ct.outputs[1].amount)}
            /\ index' = index + 1
    /\ UNCHANGED <<mempool, published, chain_height>>

(***************************************************************************)
(* Broadcast a commitment transaction to the blockchain.  The commitment   *)
(* is first signed.  The protocol allows all commitments to be broadcast,  *)
(* what happens next depends on the status of the commitment transaction.  *)
(*                                                                         *)
(* If the tx is the latest commitment transaction it can be spent later.   *)
(*                                                                         *)
(* If not, it gives the other party a chance to spend the breach remedy    *)
(* tx.                                                                     *)
(*                                                                         *)
(* TODO: We only spec CSV (self) commitment transaction.  We need to       *)
(* handle the non-CSV output being published and co-op closes.             *)
(***************************************************************************)
BroadcastCommitment(party) ==
    /\ cts # {}
    /\
        LET
            key_index == 1 \* TODO, manage key numbers
            ct == CHOOSE ct \in cts: TRUE
        IN
            \* The commitment is not already in mempool
            /\ ct \notin mempool
            \* No commitment has already been confirmed
            /\ published = {FundingTx}
            /\ mempool' = mempool \cup {[ct EXCEPT !.party_signed = TRUE]}
    /\ UNCHANGED <<cts, brs, published, index, chain_height>>

(***************************************************************************)
(* Confirm any transaction from mempool - this indeed is sparta.  Any      *)
(* mempool tx can be confirmed.  So we model just that.                    *)
(*                                                                         *)
(* The only requirement is to make sure the CSV has expired.               *)
(***************************************************************************)
ConfirmMempoolTx ==
    \E tx \in mempool:
        /\ \E o \in SeqToSet(tx.outputs):
            \/ o.type = "multisig" /\ o.csv < chain_height \* CSV expired
            \/ o.type = "p2wkh" /\ o.csv = NoCSV         \* Without a CSV
        /\ tx \notin published               \* Tx is not already confirmed
        /\ mempool' = mempool \ {tx}
        /\ chain_height' = chain_height + 1
        /\ published' = published \cup {[tx EXCEPT !.height = chain_height']}
        /\ UNCHANGED <<cts, brs, index>>

(***************************************************************************)
(* Broadcast a breach remedy transaction in response to a commitment       *)
(* transaction.                                                            *)
(*                                                                         *)
(* party is broadcasting the tx                                            *)
(***************************************************************************)
BroadcastBR ==
    /\ \E <<m, b>> \in mempool \X brs:
        /\ published = {FundingTx}  \* Channel is not closed yet
        /\ m.outputs[1].type = "multisig"
        \* Offending tx in mempool
        /\ chain_height - 1 < m.outputs[1].csv
        /\ m.party = b.party
        /\ mempool' = mempool \cup {m}
    /\ UNCHANGED <<cts, brs, index, published, chain_height>>

 
Next ==
    \/ \E d \in 1..2: SupersedeCommitmentTx(d)
    \/ \E p \in Party: BroadcastCommitment(p)
    \/ BroadcastBR
    \/ ConfirmMempoolTx

Spec == Init /\ [][Next]_<<vars>>

Liveness == WF_vars(BroadcastBR)

FairSpec == Spec /\ Liveness

\* TODO - Add BalanceInvariant: Sum of all amounts on all txs = InitialBalance

=============================================================================
