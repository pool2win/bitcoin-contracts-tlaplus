----------------------------- MODULE Contracts -----------------------------

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
Key == \A p \in Party, k \in 0..NumKey - 1: <<p, k>>

(***************************************************************************)
(* Value to capture missing CSV in output                                  *)
(***************************************************************************)
NoCSV == CHOOSE c : c \notin 0..CSV

(***************************************************************************)
(* Multisig outputs without CSV encumberance                               *)
(***************************************************************************)
MultiSigOutput == \A a, b \in Party \X Party: <<a, b, NoCSV>>

(***************************************************************************)
(* Multisig outputs with CSV encumberance                                  *)
(***************************************************************************)
MultiSigWithCSVOutput == \A a, b \in Party \X Party: <<a, b, CSV>>

(***************************************************************************)
(* P2PKH outputs, without encumbrance                                      *)
(***************************************************************************)
P2PKH == Key

AllOutput == MultiSigOutput \cup MultiSigWithCSVOutput \cup P2PKH

NoOutput == CHOOSE o : o \notin AllOutput

(***************************************************************************)
(* Set of all signatures for all commit txs.  The signature in real world  *)
(* is related to the commit transaction, however, leave out this           *)
(* complication of how the signature is generated.  If there is a          *)
(* signature by a key on a tx, it is assumed it is correctly signed as per *)
(* bitcoin's requirements                                                  *)
(***************************************************************************)
Sig == \A p \in Party, k \in 0..NumKey - 1: <<p, k>>

(***************************************************************************)
(* Value to capture unsigned transactions                                  *)
(***************************************************************************)
NoSig == CHOOSE s : s \notin Sig

(***************************************************************************)
(* Define the commitment tx type.  We don't have HTLCs yet.  We also don't *)
(* filter outputs to the party here.  We leave that for actions, or we'll  *)
(* add the filter when needed.                                             *)
(***************************************************************************)
CommitmentTx == [
                    party |-> Party,
                    outputs |-> Seq(AllOutput),
                    local_sig |-> Sig \cup NoSig,
                    remote_sig |-> Sig \cup NoSig
                ]


VARIABLES
    commitment_txs     \* The set of all commiment transactions for both parties

vars == <<commitment_txs>>
-----------------------------------------------------------------------------

Init ==
    /\ commitment_txs = \A p \in Party: [p -> <<>>]

TypeInvariant ==
    /\ commitment_txs \in CommitmentTx

=============================================================================
