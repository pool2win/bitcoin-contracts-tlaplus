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
(* focusses on the various commitment transaction and their lifecycle in   *)
(* response to interaction between parties and the blockchain.             *)
(*                                                                         *)
(* We ignore the details of how transactions are signed and just mark      *)
(* transactions as signed.  This lets us focus on the specifying the       *)
(* behaviour of the commitment transactions without dealing with lower     *)
(* level complexities.                                                     *)
(*                                                                         *)
(* TODO: We don't track balances yet.  Need to do that and don't go into   *)
(* certain states depending on the balance checks                          *)
(*                                                                         *)
(* TODO: Add HTLCs! Now that will be fun!                                  *)
(***************************************************************************)

EXTENDS Integers,
        TLC,
        Sequences,
        FiniteSets

CONSTANTS
    CSV,        \* The csv value to use in contracts
    Height,     \* The height up to which we run the spec
    NumTxs      \* The number of commitment txs we want

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

CT == [index |-> 0..NumTxs,
       multisig |-> MultiSigWithCSV, pk |-> P2WKH,
       local_sig |-> Sig \cup {NoSig},
       remote_sig |-> Sig \cup {NoSig}]

PublishId == {<<p, i, h>>: p \in Party, i \in 0..NumTxs, h \in 0..Height}      
NoSpend == <<>>
-----------------------------------------------------------------------------

VARIABLES
    alice_cts,      \* Commitment tx for alice
    bob_cts,        \* Commitment tx for bob
    alice_brs,      \* Breach remedy transactions for alice
    bob_brs,        \* Breach remedy transactions for bob
    mempool_ct,     \* The CT that has been broadcasted. 
                    \* TODO: Turn into Seq. More than one can be in mempool.
    published_ct    \* The CT that has been included in a block and confirmed.
       

vars == <<alice_cts, bob_cts, alice_brs, bob_brs, mempool_ct, published_ct>>

(***************************************************************************)
(* Helper function to get other party                                      *)
(***************************************************************************)
OtherParty(party) == CHOOSE p \in Party: p # party

(***************************************************************************)
(* Create a commitment transaction given the party, index and key to use.  *)
(***************************************************************************)
CreateCT(party, index, key_num) ==
        [index |-> index,
         multisig |-> <<party, OtherParty(party), CSV>>,
         pk |-> <<party, key_num>>,
         local_sig |-> NoSig,
         remote_sig |-> <<OtherParty(party), key_num>>]

Init ==
    /\ alice_cts = {CreateCT("alice", 0, 0)}
    /\ bob_cts = {CreateCT("bob", 0, 0)}
    /\ alice_brs = {}
    /\ bob_brs = {}
    /\ mempool_ct = NoSpend
    /\ published_ct = NoSpend

TypeInvariant ==
        /\ \A ct \in alice_cts \cup bob_cts:
            /\ ct.index \in 0..NumTxs
            /\ ct.local_sig \in Sig \cup {NoSig}
            /\ ct.remote_sig \in Sig \cup {NoSig}
            /\ ct.pk \in P2WKH
            /\ ct.multisig \in MultiSigWithCSV
        /\ \A br \in alice_brs \cup bob_brs:
            /\ br.index \in 0..NumTxs
            /\ br.pk \in P2WKH
        /\ mempool_ct \in PublishId \cup {NoSpend}
        /\ published_ct \in PublishId \cup {NoSpend}

-----------------------------------------------------------------------------

MaxIndex(party_cts) ==
    (CHOOSE x \in party_cts: \A y \in party_cts: x.index >= y.index).index

(***************************************************************************)
(* Create first commitment transactions for given parties                  *)
(*                                                                         *)
(* Breach remedy transactions are pre-signed transactions instead of they  *)
(* private key being sent over to the other party.                         *)
(***************************************************************************)
SupersedeCommitmentTx(index) ==
    /\ mempool_ct # NoSpend      \* Stop creating new CTs once FT is spent
    /\
        LET key_index == 1
        IN
            /\ index > MaxIndex(alice_cts)
            /\ index > MaxIndex(bob_cts)
            /\ alice_cts' = alice_cts \cup {CreateCT("alice", index, key_index)}
            /\ bob_cts' = bob_cts \cup {CreateCT("bob", index, key_index)}
            /\ alice_brs' = alice_brs \cup {[index |-> index, pk |-> <<"bob", key_index>>]}
            /\ bob_brs' = bob_brs \cup {[index |-> index, pk |-> <<"alice", key_index>>]}
    /\ UNCHANGED <<mempool_ct, published_ct>>

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
PublishCommitment(party, index, height) ==
    /\ mempool_ct = NoSpend
    /\ mempool_ct' = <<party, index, height>>
    /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs, published_ct>>

(****************************************************************************
Publish a breach remedy transaction in response to a commitment
transaction.

party is publishing the breach remedy tx when it is on index CT, and
the chain is on height.

This tx is immediately published on chain.

TODO: We skip the BR going through the mempool and confirm it
immeidiately.  This can be improved too.
****************************************************************************)
PublishBR(party, index, height) ==
    LET cts == IF party = "alice" THEN alice_cts ELSE bob_cts
    IN
        /\ published_ct = NoSpend                   \* No CT is confirmed on chain yet
        /\ mempool_ct # NoSpend                     \* Only if some CT has been published
        /\ mempool_ct[1] = OtherParty(party)        \* CT was published by the other party
        /\ mempool_ct[2] < MaxIndex(cts)            \* Revoked CT was published
        /\ mempool_ct[2] = index                    \* We need to use the BR from the same index
        /\ height - mempool_ct[2] < CSV             \* Can only publish BR if CSV hasn't expired
        /\ published_ct' = <<party, index, height>> \* Record which index was published at what height
    /\ UNCHANGED <<alice_cts, bob_cts, alice_brs, bob_brs, mempool_ct>>

 
Next ==
    \/ \E i \in 0..NumTxs: SupersedeCommitmentTx(i)
    \/ \E i \in 0..NumTxs, p \in Party, h \in 0..Height: PublishCommitment(p, i, h)
    \/ \E i \in 0..NumTxs, p \in Party, h \in 0..Height: PublishBR(p, i, h)

    
    
Spec == Init /\ [][Next]_<<vars>>
=============================================================================
