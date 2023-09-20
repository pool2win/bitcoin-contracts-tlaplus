-------------------------------- MODULE htlc --------------------------------

(***************************************************************************)
(* Specifications for the HTLC sending and forwarding.  The protocol is    *)
(* composed of a number of actions like initiate, update, expire.  These   *)
(* actions collectively specify how the state of each node and the balance *)
(* on each channel can change.                                             *)
(***************************************************************************)

EXTENDS Integers

(***************************************************************************)
(* Channel is considered directional in this specification. So <<a, b>> is *)
(* a channel and so is <<b, a>>                                            *)
(***************************************************************************)
CONSTANTS Channel, InitialBalance

VARIABLES balance, commit_txs
-----------------------------------------------------------------------------

vars == <<balance>>

node_states == {"ready", "pending", "in_latest_commit_tx", "prev_commit_tx_revoked"}

Init == 
    /\ \A c \in Channel: balance[c] = CHOOSE b: b \in InitialBalance \* Initialise with any given initial balance

TypeInvariant == 
    /\ balance \in [Channel -> Int]
    \* There are no constraints in the protocol on the state of the counterparties states. So all combinations are allowed
    /\ commit_txs \in [Channel -> node_states \X node_states]
    
-----------------------------------------------------------------------------

(*
When invoked on channel <<a, b>>. The commit transaction of b is affected.
*)
update_add_htlc(channel, amount) ==
    /\ commit_txs[channel] = "ready"
    /\ commit_txs' = [commit_txs EXCEPT ![channel] = "pending"]
    
=============================================================================

