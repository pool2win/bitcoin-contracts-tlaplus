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
(* focuss on the various commitment transaction and their lifecycle in     *)
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
(* Multisig outputs without CSV encumberance                               *)
(***************************************************************************)
MultiSig == Party \X Party \X {NoCSV}

(***************************************************************************)
(* Multisig outputs with CSV encumberance                                  *)
(***************************************************************************)
MultiSigWithCSV == Party \X Party \X {CSV}

(***************************************************************************)
(* P2WKH outputs, without encumbrance                                      *)
(***************************************************************************)
P2WKH == Key

(***************************************************************************)
(* Set of all signatures for all commit txs.  The signature in real world  *)
(* is related to the commit transaction.  However, we leave out this       *)
(* complication of how the signature is generated.  If there is a          *)
(* signature by a key on a tx, it is assumed it is correctly signed as per *)
(* bitcoin's requirements                                                  *)
(***************************************************************************)
Sig == {<<p, k>>: p \in Party, k \in 0..NumKey - 1}

(***************************************************************************)
(* Value to capture unsigned transactions                                  *)
(***************************************************************************)
NoSig == CHOOSE s : s \notin Sig

CT == [index |-> Int,
       multisig |-> MultiSigWithCSV, pk |-> P2WKH,
       local_sig |-> Sig \cup {NoSig},
       remote_sig |-> Sig \cup {NoSig},
       balance |-> 0..InitialBalance]

OnChainTx == [party |-> Party,
              index |-> Int,
              height |-> Int]

NoSpendHeight == -1

-----------------------------------------------------------------------------

VARIABLES
    alice_cts,      \* Commitment tx for alice
    bob_cts,        \* Commitment tx for bob
    alice_brs,      \* Breach remedy transactions for alice
    bob_brs,        \* Breach remedy transactions for bob
    mempool,     \* The CT txs that have been broadcasted.
    published,   \* The CT that has been included in a block and confirmed.
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
CreateCT(party, i, key_num, balance) ==
        [party |-> party,
         index |-> i,
         multisig |-> <<party, OtherParty(party), CSV>>,
         pk |-> <<party, key_num>>,
         local_sig |-> NoSig,
         remote_sig |-> <<OtherParty(party), key_num>>,
         balance |-> balance]

CreateOnChainTx(party, ix, height) ==
        [party |-> party,
         height |-> height,
          index |-> ix]


Init ==
    \* Balanced channel to start with
    /\ alice_cts = {CreateCT("alice", 0, 0, InitialBalance)}
    /\ bob_cts = {CreateCT("bob", 0, 0, InitialBalance)}
    /\ alice_brs = {}
    /\ bob_brs = {}
    /\ mempool = {}
    /\ published = {}
    /\ index = 1
    /\ chain_height = 1 \* The genesis block is the FT

TypeInvariant ==
        /\ \A ct \in alice_cts \cup bob_cts \cup mempool:
            /\ ct.party \in Party
            /\ ct.index \in Nat
            /\ ct.local_sig \in Sig \cup {NoSig}
            /\ ct.remote_sig \in Sig \cup {NoSig}
            /\ ct.pk \in P2WKH
            /\ ct.multisig \in MultiSigWithCSV
        /\ \A br \in alice_brs \cup bob_brs:
            /\ br.index \in Nat
            /\ br.pk \in P2WKH
        /\ \A p \in published:
             /\ p.party \in Party
             /\ p.index \in Int
             /\ p.height \in Int
        /\ index \in Nat

-----------------------------------------------------------------------------

MaxIndex(party_cts) ==
    (CHOOSE x \in party_cts: \A y \in party_cts: x.index >= y.index).index

LastCT(party_cts) ==
    CHOOSE ct \in party_cts: \A y \in party_cts: ct.index >= y.index

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
            key_index == 1
            last_alice_ct == LastCT(alice_cts)
            last_bob_ct == LastCT(bob_cts)
        IN
            \* Create CTs till channel is not closed
            /\ published = {}
            /\ last_alice_ct.balance + delta > 0
            /\ last_bob_ct.balance - delta > 0
            /\ alice_cts' = alice_cts \cup
                    {CreateCT("alice", index, key_index,
                        last_alice_ct.balance + delta)}
            /\ bob_cts' = bob_cts \cup
                    {CreateCT("bob", index, key_index,
                        last_alice_ct.balance - delta)}
            /\ alice_brs' = alice_brs \cup
                    {[index |-> index, pk |-> <<"bob", key_index>>]}
            /\ bob_brs' = bob_brs \cup
                    {[index |-> index, pk |-> <<"alice", key_index>>]}
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
            cts == IF party = "alice" THEN alice_cts ELSE bob_cts
            ct == CHOOSE ct \in cts: TRUE
        IN
            /\ ct \notin mempool
            /\ mempool' = mempool \cup {ct}
    /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs,
                    published, index, chain_height>>

(***************************************************************************)
(* Publish any transaction from mempool - this indeed is sparta.  Any      *)
(* mempool tx can be confirmed.  So we model just that.  The only rule is  *)
(* to make sure the CSV has expired, and that is handled at the time of    *)
(* inserting the tx into mempool                                           *)
(***************************************************************************)
ConfirmMempoolTx ==
    \E tx \in mempool:
        /\ chain_height' = chain_height + 1
        /\ published' = published \cup
                {CreateOnChainTx(tx.party, tx.index, chain_height')}
        /\ mempool' = mempool \ {tx}
        /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs,
                        index>>

(***************************************************************************)
(* Publish a breach remedy transaction in response to a commitment         *)
(* transaction.                                                            *)
(*                                                                         *)
(* party is publishing the breach remedy tx when it is on index CT, and    *)
(* the chain is on height.                                                 *)
(*                                                                         *)
(* This tx is immediately published on chain.                              *)
(*                                                                         *)
(* TODO: We skip the BR going through the mempool and confirm it           *)
(* immediately.  This can be improved too.                                 *)
(***************************************************************************)
BroadcastBR(party) ==
    /\
        LET
            cts == IF party = "alice" THEN alice_cts ELSE bob_cts
        IN
            \E in_mempool \in mempool:
                \* CT was broadcast by the other party
                /\ in_mempool.party = OtherParty(party)
                \* Revoked CT was broadcast
                /\ in_mempool.index < MaxIndex(cts)
                \* `party` already signed the ct as remote sig
                /\ in_mempool.remote_sig[1] = party
                \* CSV hasn't expired - given FT is at height 1
                /\ chain_height < CSV
                /\ mempool' = mempool \cup {in_mempool}
    /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs,
                    mempool, index, published, chain_height>>

 
Next ==
    \/ \E d \in {-1, 1}: SupersedeCommitmentTx(d)
    \/ \E p \in Party: BroadcastCommitment(p)
    \/ \E p \in Party: BroadcastBR(p)
    \/ ConfirmMempoolTx

Spec == Init /\ [][Next]_<<vars>>

\*Liveness == \E p \in Party, d \in {-1, 1}:
\*                    WF_vars(PublishBR(p) \/ SupersedeCommitmentTx(d))
Liveness == WF_vars(ConfirmMempoolTx)

FairSpec == Spec /\ Liveness

=============================================================================
