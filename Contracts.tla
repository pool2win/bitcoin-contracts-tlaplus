----------------------------- MODULE Contracts -----------------------------

(***************************************************************************)
(* This spec captures the behaviour of commitment transactions on the two  *)
(* sides of a Lightning channel.                                           *)
(*                                                                         *)
(* We model the various kinds of outputs a commitment transactions will    *)
(* have over its lifetime.                                                 *)
(*                                                                         *)
(* The state of the commitment transaction changes in reponse to the       *)
(* various actions like supercede, spend, revoke etc are taken.            *)
(*                                                                         *)
(* We also do not deal with the communication protocol between nodes for   *)
(* creating and updating commitment transactions.  This spec only focusses *)
(* on the various commitment transaction created, revoked, spent to open,  *)
(* close, force close or penalise.                                         *)
(*                                                                         *)
(* We ignore the details of how transactions are signed and just mark      *)
(* transactions as signed.  This lets us focus on the specifying the       *)
(* behaviour of the commitment transactions without dealing with lower     *)
(* level complexities.                                                     *)
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
(* Sequences utility                                                       *)
(***************************************************************************)

SeqOf(set, n) ==
  (***************************************************************************)
  (* All sequences up to length n with all elements in set.  Includes empty  *)
  (* sequence.                                                               *)
  (***************************************************************************)
  UNION {[1..m -> set] : m \in 0..n}

ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (*************************************************************************)
  { s[i] : i \in DOMAIN s }

Contains(s, e) ==
  (**************************************************************************)
  (* TRUE iff the element e \in ToSet(s).                                   *)
  (**************************************************************************)
  \E i \in 1..Len(s) : s[i] = e

Last(s) == s[Len(s)]
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
(* P2PKH outputs, without encumbrance                                      *)
(***************************************************************************)
P2PKH == Key

(***************************************************************************)
(* Set of all signatures for all commit txs.  The signature in real world  *)
(* is related to the commit transaction, however, leave out this           *)
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
       multisig |-> MultiSigWithCSV, pk |-> P2PKH,
       local_sig |-> Sig \cup {NoSig},
       remote_sig |-> Sig \cup {NoSig}]

-----------------------------------------------------------------------------

VARIABLES
    alice_cts,      \* Commitment tx for alice
    bob_cts,        \* Commitment tx for bob
    alice_brs,      \* Breach remedy transactions for alice
    bob_brs         \* Breach remedy transactions for bob

vars == <<alice_cts, bob_cts, alice_brs, bob_brs>>

(***************************************************************************)
(* Helper function to get other party                                      *)
(***************************************************************************)
OtherParty(party) == CHOOSE p \in Party: p # party

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

(***************************************************************************)
(* We don't define transactions using a function because using variables   *)
(* as functions become hard to work with in TLA+                           *)
(***************************************************************************)
TypeInvariant ==
        /\ \A ct \in alice_cts \cup bob_cts:
            /\ ct.index \in 0..NumTxs
            /\ ct.local_sig \in Sig \cup {NoSig}
            /\ ct.remote_sig \in Sig \cup {NoSig}
            /\ ct.pk \in P2PKH
            /\ ct.multisig \in MultiSigWithCSV
        /\ \A br \in alice_brs \cup bob_brs:
            /\ br.index \in 0..NumTxs
            /\ br.pk \in P2PKH

-----------------------------------------------------------------------------

(***************************************************************************)
(* Create first commitment transactions for given parties                  *)
(*                                                                         *)
(* Breach remedy transactions are pre-signed transactions instead of they  *)
(* private key being sent over to the other party.                         *)
(***************************************************************************)
SupercedeCommitmentTx(index) ==
    LET key_index == 1
    IN
        /\ index = Cardinality(alice_cts)
        /\ Cardinality(alice_cts) > 0 /\ Cardinality(bob_cts) > 0
        /\ Cardinality(alice_cts) < NumTxs /\ Cardinality(bob_cts) < NumTxs
        /\ alice_cts' = alice_cts \cup {CreateCT("alice", index, key_index)}
        /\ bob_cts' = bob_cts \cup {CreateCT("bob", index, key_index)}
        /\ alice_brs' = alice_brs \cup {[index |-> index, pk |-> <<"bob", key_index>>]}
        /\ bob_brs' = bob_brs \cup {[index |-> index, pk |-> <<"alice", key_index>>]}

(***************************************************************************)
(* Publish a commitment transaction to the blockchain.  The commitment is  *)
(* first signed.  The protocol allows all commitments to be published,     *)
(* what happens next depends on the status of the commitment transaction.  *)
(*                                                                         *)
(* If the tx is the latest commitment transaction it is succesfuly spend.  *)
(*                                                                         *)
(* If not, it gives the other party a chance to spend the breach remedy    *)
(* tx.                                                                     *)
(***************************************************************************)
\*PublishCommitment(party, party_cts, ct) ==
\*    /\ IF ct.index = Cardinality(party_cts)
\*       THEN SpendCommitment(ct)
\*       ELSE PublishPenalty(ct)

Next ==
    /\ \exists index \in 0..NumTxs: SupercedeCommitmentTx(index)
\*    /\ \exists ct \in alice_cts: PublishCommitment("alice", alice_cts, ct)
\*    /\ \exists ct \in bob_cts: PublishCommitment("bob", bob_cts, ct)
    
    
Spec == Init /\ [][Next]_<<vars>>
=============================================================================
