----------------------------- MODULE Contracts -----------------------------

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
    CSV,            \* The csv value to use in contracts
    InitialBalance  \* Initial balances for alice and bob

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
Output == [type: {"multisig", "p2wkh"},
           party: Party,
           csv: {CSV} \cup {NoCSV},
           amount: 0..InitialBalance*2] \* All the balance can be on one side

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
(* Transaction record.                                                     *)
(*                                                                         *)
(* TODO: Track output being spent.                                         *)
(***************************************************************************)
Tx == [party: Party,
      index: Int,
      height: Int,
      outputs: Seq(Output),
      party_signed: BOOLEAN,
      other_party_signed: BOOLEAN]

-----------------------------------------------------------------------------

VARIABLES
    alice_cts,      \* Commitment tx for alice
    bob_cts,        \* Commitment tx for bob
    alice_brs,      \* Breach remedy transactions for alice
    bob_brs,        \* Breach remedy transactions for bob
    mempool,        \* The CT txs that have been broadcasted.
    published,      \* The CT that has been included in a block and confirmed.
    index,
    chain_height

vars == <<alice_cts, bob_cts, alice_brs, bob_brs, mempool, published,
          chain_height, index>>

(***************************************************************************)
(* Helper function to get other party                                      *)
(***************************************************************************)
OtherParty(party) == CHOOSE p \in Party: p # party

(***************************************************************************)
(* Create a commitment transaction given the party, index and key to use.  *)
(***************************************************************************)
CreateCT(party, i, key_num, amount, other_amount) ==
        [party |-> party,
         index |-> i,
         height |-> NoSpendHeight,
         outputs |-> <<CreateRSMCOutput(party, amount),
                      CreatePKOutput(OtherParty(party), other_amount)>>,
        party_signed |-> FALSE,
        other_party_signed |-> TRUE]

(***************************************************************************)
(* Breach remedy transactions are handled as presigned transactions        *)
(* instead of by passing private keys around.  This is different from the  *)
(* LN paper.                                                               *)
(***************************************************************************)
CreateBR(party, i, amount) ==
        [party |-> party,
         index |-> i,
         height |-> NoSpendHeight,
         outputs |-> <<CreatePKOutput(OtherParty(party), amount)>>,
         party_signed |-> TRUE,
         other_party_signed |-> FALSE]

Init ==
    \* Balanced channel to start with
    /\ alice_cts = {CreateCT("alice", 0, 0, InitialBalance, 0)}
    /\ bob_cts = {CreateCT("bob", 0, 0, 0, InitialBalance)}
    /\ alice_brs = {CreateBR("alice", 0, InitialBalance)}
    /\ bob_brs = {CreateBR("bob", 0, InitialBalance)}
    /\ mempool = {}
    /\ published = {}
    /\ index = 1
    /\ chain_height = 1 \* The genesis block is the FT

TypeInvariant ==
    /\ index \in Nat
    /\ alice_cts \in SUBSET Tx
    /\ bob_cts \in SUBSET Tx
    /\ alice_brs \in SUBSET Tx
    /\ bob_brs \in SUBSET Tx
    /\ mempool \in SUBSET Tx
    /\ published \in SUBSET Tx

-----------------------------------------------------------------------------

LastCT(party_cts) ==
    CHOOSE ct \in party_cts: \A y \in party_cts: ct.index >= y.index

MaxIndex(party_cts) ==
    (LastCT(party_cts)).index

AnyCT == (CHOOSE ct \in alice_cts \cup bob_cts: TRUE)

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
            key_index == 1 \* TODO, manage key numbers
            last_alice_ct == LastCT(alice_cts)
            last_bob_ct == LastCT(bob_cts)
        IN
            \* Create CTs till channel is not closed
            /\ published = {}
            /\ last_alice_ct.outputs[1].amount - delta > 0
            /\ last_alice_ct.outputs[2].amount + delta <= InitialBalance
            /\ alice_cts' = alice_cts \cup
                    {CreateCT("alice", index, key_index,
                        last_alice_ct.outputs[1].amount - delta,
                        last_alice_ct.outputs[2].amount + delta)}
            /\ bob_cts' = bob_cts \cup
                    {CreateCT("bob", index, key_index,
                        last_bob_ct.outputs[1].amount + delta,
                        last_bob_ct.outputs[2].amount - delta)}
            /\ alice_brs' = alice_brs \cup
                        {CreateBR("alice", index, last_alice_ct.outputs[1].amount)}
            /\ bob_brs' = bob_brs \cup
                        {CreateBR("bob", index, last_alice_ct.outputs[1].amount)}
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
    /\ alice_cts # {}
    /\ bob_cts # {}
    /\
        LET
            key_index == 1 \* TODO, manage key numbers
            cts == IF party = "alice" THEN alice_cts ELSE bob_cts
            ct == CHOOSE ct \in cts: TRUE
        IN
            \* The commitment is not already in mempool
            /\ ct \notin mempool
            \* No commitment has already been confirmed
            /\ published = {}
            /\ mempool' = mempool \cup {ct}
    /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs,
                    published, index, chain_height>>

(***************************************************************************)
(* Confirm any transaction from mempool - this indeed is sparta.  Any      *)
(* mempool tx can be confirmed.  So we model just that.  The only rule is  *)
(* to make sure the CSV has expired, and that is handled at the time of    *)
(* inserting the tx into mempool                                           *)
(***************************************************************************)
ConfirmMempoolTx ==
    \E tx \in mempool:
        /\ tx \notin published               \* Tx is not already confirmed
        /\ mempool' = mempool \ {tx}
        /\ chain_height' = chain_height + 1
        /\ published' = published \cup {[tx EXCEPT !.height = chain_height']}
        /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs,
                    index>>

(***************************************************************************)
(* Broadcast a breach remedy transaction in response to a commitment       *)
(* transaction.                                                            *)
(*                                                                         *)
(* party is broadcasting the tx                                            *)
(***************************************************************************)
BroadcastBR(party) ==
    /\
        LET
            cts == IF party = "alice" THEN alice_cts ELSE bob_cts
            brs == IF party = "alice" THEN bob_brs ELSE alice_brs
        IN
            \E in_mempool \in mempool:
                \* CT was broadcast by the other party
                /\ in_mempool.outputs[1].party = OtherParty(party)
                \* Revoked CT was broadcast
                /\ in_mempool.index < MaxIndex(cts)
                \* This party already signed the ct as local sig
                /\ in_mempool.other_party_signed = TRUE
                \* CSV hasn't expired - given FT is at height 1
                /\ chain_height < CSV
                /\ mempool' = mempool \cup {CHOOSE b \in brs: b.index = in_mempool.index}
    /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs,
                    index, published, chain_height>>

 
Next ==
    \/ \E d \in 1..2: SupersedeCommitmentTx(d)
    \/ \E p \in Party: BroadcastCommitment(p)
    \/ \E p \in Party: BroadcastBR(p)
    \/ ConfirmMempoolTx

Spec == Init /\ [][Next]_<<vars>>

\*Liveness == \E p \in Party, d \in {-1, 1}:
\*                    WF_vars(PublishBR(p) \/ SupersedeCommitmentTx(d))
Liveness == \E d \in {1}: WF_vars(SupersedeCommitmentTx(d))

FairSpec == Spec /\ Liveness

\* TODO - Add BalanceInvariant: Sum of all amounts on all txs = InitialBalance

=============================================================================
