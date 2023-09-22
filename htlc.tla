-------------------------------- MODULE htlc --------------------------------

(***************************************************************************)
(* Specifications for the HTLC sending and forwarding. The protocol is     *)
(* composed of actions like initiate, update, expire. These actions        *)
(* specify how the state of each node and the balance on each channel is   *)
(* allowed to change in response to handling HTLC messages                 *)
(***************************************************************************)

EXTENDS Integers,
        TLC

CONSTANTS Node, Channel, InitialBalance

(***************************************************************************)
(* Channels are unidirectional in the spec.  This helps us track states    *)
(* and balances for the purposes of the specifications.                    *)
(***************************************************************************)
VARIABLES htcl_states,
          channel_balances
          
-----------------------------------------------------------------------------

vars == <<htcl_states, channel_balances>>

update_states == {"ready", 
                  "pending", 
                  "in_latest_commit_tx", 
                  "prev_commit_tx_revoked"}


(***************************************************************************)
(* Initialise with an initial balance and ready state                      *)
(***************************************************************************)
Init == 
    /\ channel_balances = [<<m, n>> \in Channel |-> CHOOSE b \in InitialBalance: TRUE]
    /\ htcl_states = [<<m, n>> \in Channel |-> "ready"]

TypeInvariant ==
    /\ Channel \in Node \X Node                                 \* channels are between nodes 
    /\ channel_balances \in [Node \X Node -> InitialBalance]    \* channel balance
    /\ htcl_states \in [Node \X Node -> update_states]       \* channels htlc state
    
-----------------------------------------------------------------------------

(*
When invoked on channel <<a, b>>. The commit transaction of b is affected.
*)
update_add_htlc(m, n, amount) ==
    /\ htcl_states[<<m, n>>] = "ready"    \* Commit tx state should be ready
    /\ channel_balances[<<m, n>>] > 0        \* Forward only if there is some balance
    /\ htcl_states' = [htcl_states EXCEPT ![<<m, n>>] = "pending"] \* Change state to pending
    /\ UNCHANGED channel_balances
    
-----------------------------------------------------------------------------

Next ==
    \/ \exists <<m, n>> \in Channel, a \in InitialBalance:
            /\ update_add_htlc(m, n, a)
        
Spec == 
    /\ Init
    /\ [][Next]_<<vars>>
=============================================================================

