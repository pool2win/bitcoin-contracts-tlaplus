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
        Sequences

CONSTANTS
    CSV,        \* The csv value to use in contracts
    Height      \* The height up to which we run the spec

(***************************************************************************)
(* Channel contracts only ever have two parties                            *)
(***************************************************************************)
 Party == {"alice", "bob"}

(***************************************************************************)
(* For the first revocation we only need two keys per party                *)
(***************************************************************************)
 NumKey == 2

(***************************************************************************)
(* Set of all keys                                                         *)
(***************************************************************************)
Key == {<<p, k>>: p \in Party, k \in 0..NumKey - 1}

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

AllOutput == MultiSig \cup MultiSigWithCSV \cup P2PKH

NoOutput == CHOOSE o : o \notin AllOutput

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

-----------------------------------------------------------------------------

VARIABLES
    outputs,     \* The set of all commiment transactions for both parties
    local_sigs,
    remote_sigs

vars == <<outputs, local_sigs, remote_sigs>>

Init ==
    /\ outputs = [p \in Party |-> <<>>]
    /\ local_sigs = [p \in Party |-> NoSig]
    /\ remote_sigs = [p \in Party |-> NoSig]

(***************************************************************************)
(* We don't define transactions using a function because using variables   *)
(* as functions become hard to work with in TLA+                           *)
(***************************************************************************)
TypeInvariant ==
        /\ outputs \in [Party -> Seq(AllOutput)]
        /\ local_sigs \in [Party -> Sig \cup {NoSig}]
        /\ remote_sigs \in [Party -> Sig \cup {NoSig}]

-----------------------------------------------------------------------------

(***************************************************************************)
(* Helper function to get other party                                      *)
(***************************************************************************)
OtherParty(party) == CHOOSE p \in Party: p # party

(***************************************************************************)
(* Create first commitment transactions for given parties                  *)
(***************************************************************************)
CreateFirstCommitmentTx(party) ==
        /\ outputs[party] = <<>>
        /\ outputs' = [outputs EXCEPT ![party] =
                                @ \o <<<<party, OtherParty(party), CSV>>,
                                       <<OtherParty(party), 0>>>>]
        /\ local_sigs' = [local_sigs EXCEPT ![party] = <<party, 0>>]
        /\ remote_sigs' = [remote_sigs EXCEPT ![party] = <<OtherParty(party), 0>>]

(***************************************************************************)
(* Party p spends their commitment transaction.                            *)
(*                                                                         *)
(* If the tx is the latest commitment transaction it is succesfuly spend.  *)
(*                                                                         *)
(* If not, ti gives the other party a chance to spend the breach remedy    *)
(* tx.                                                                     *)
(***************************************************************************)
\* SpendCommitmentTx(p, tx)

Next ==
    \/ \exists p \in Party: CreateFirstCommitmentTx(p)

Spec == Init /\ [][Next]_<<vars>>
=============================================================================
