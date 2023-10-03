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
    Height,         \* The height up to which we run the spec
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

-----------------------------------------------------------------------------

VARIABLES
    alice_cts,      \* Commitment tx for alice
    bob_cts,        \* Commitment tx for bob
    alice_brs,      \* Breach remedy transactions for alice
    bob_brs,        \* Breach remedy transactions for bob
    mempool,     \* The CT txs that have been broadcasted.
    published,   \* The CT that has been included in a block and confirmed.
    index
       

vars == <<alice_cts, bob_cts, alice_brs, bob_brs, mempool, published, index>>

(***************************************************************************)
(* Helper function to get other party                                      *)
(***************************************************************************)
OtherParty(party) == CHOOSE p \in Party: p # party

(***************************************************************************)
(* Create a commitment transaction given the party, index and key to use.  *)
(***************************************************************************)
CreateCT(party, i, key_num, balance) ==
        [index |-> i,
         multisig |-> <<party, OtherParty(party), CSV>>,
         pk |-> <<party, key_num>>,
         local_sig |-> NoSig,
         remote_sig |-> <<OtherParty(party), key_num>>,
         balance |-> balance]

CreateOnChainTx(party, ix, height) ==
        [party |-> party,
         index |-> ix,
         height |-> height]

Init ==
    \* Balanced channel to start with
    /\ alice_cts = {CreateCT("alice", 0, 0, InitialBalance)}
    /\ bob_cts = {CreateCT("bob", 0, 0, InitialBalance)}
    /\ alice_brs = {}
    /\ bob_brs = {}
    /\ mempool = {}
    /\ published = {}
    /\ index = 1

TypeInvariant ==
        /\ \A ct \in alice_cts \cup bob_cts:
            /\ ct.index \in Nat
            /\ ct.local_sig \in Sig \cup {NoSig}
            /\ ct.remote_sig \in Sig \cup {NoSig}
            /\ ct.pk \in P2WKH
            /\ ct.multisig \in MultiSigWithCSV
        /\ \A br \in alice_brs \cup bob_brs:
            /\ br.index \in Nat
            /\ br.pk \in P2WKH
        /\ \A p \in mempool:
             /\ p.party \in Party
             /\ p.index \in Int
             /\ p.height \in 0..Height
        /\ \A p \in published:
             /\ p.party \in Party
             /\ p.index \in Int
             /\ p.height \in 0..Height
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
    /\ UNCHANGED <<mempool, published>>

(***************************************************************************)
(* Publish a commitment transaction to the blockchain.  The commitment is  *)
(* first signed.  The protocol allows all commitments to be published,     *)
(* what happens next depends on the status of the commitment transaction.  *)
(*                                                                         *)
(* If the tx is the latest commitment transaction it is succesfuly spend.  *)
(*                                                                         *)
(* If not, it gives the other party a chance to spend the breach remedy    *)
(* tx.                                                                     *)
(*                                                                         *)
(* TODO: We only spec CSV (self) commitment transaction. We need to handle *)
(* the non-CSV output being published and co-op closes.                    *)
(***************************************************************************)
BroadcastCommitment(party, height) ==
    /\ alice_cts # {}
    /\ bob_cts # {}
    /\
        LET
            i == AnyCT.index
            tx == CreateOnChainTx(party, i, height)
        IN
            /\ tx \notin mempool
            /\ tx \notin published
            /\ mempool' = mempool \cup {tx}
    /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs,
                    published, index>>

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
PublishBR(party, height) ==
    /\
        LET
            cts == IF party = "alice" THEN alice_cts ELSE bob_cts
        IN
            \E in_mempool \in mempool:
                /\ published = {}                   \* No CT is confirmed on chain yet
                /\ in_mempool.party = OtherParty(party)    \* CT was broadcast by the other party
                /\ in_mempool.index < MaxIndex(cts)        \* Revoked CT was broadcast
                /\ height - in_mempool.index < CSV         \* CSV hasn't expired
                \* Record which index was published at what height
                /\ published' = published \cup
                                    {CreateOnChainTx(party, in_mempool.index, height)}
    /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs,
                    mempool, index>>

 
Next ==
    \/ \E d \in {-1, 1}: SupersedeCommitmentTx(d)
    \/ \E p \in Party, h \in 0..Height: BroadcastCommitment(p, h)
    \/ \E p \in Party, h \in 0..Height: PublishBR(p, h)

Spec == Init /\ [][Next]_<<vars>>

Liveness == \E p \in Party, h \in 0..Height:
                    WF_vars(PublishBR(p, h))

FairSpec == Spec /\ Liveness

=============================================================================
