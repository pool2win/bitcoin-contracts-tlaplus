-------------------------------- MODULE htlc --------------------------------

(***************************************************************************)
(* Specifications for the HTLC sending and forwarding. The protocol is     *)
(* composed of actions like initiate, update, expire. These actions        *)
(* specify how the state of each node and the balance on each channel is   *)
(* allowed to change in response to handling HTLC messages                 *)
(***************************************************************************)

EXTENDS Integers,
        TLC

CONSTANTS Node, Channel, ChannelId, InitialBalance

(***************************************************************************)
(* Channels are unidirectional in the spec.  This helps us track states    *)
(* and balances for the purposes of the specifications.                    *)
(* Channel balances are tracked for sender.                                *)
(* htlc balances are tracked for receiver.                                 *)
(***************************************************************************)
VARIABLES htlc_states,
          channel_balances,
          htlc_balances
          
-----------------------------------------------------------------------------

vars == <<htlc_states, channel_balances, htlc_balances>>

update_states == {"ready", 
                  "pending", 
                  "in_latest_commit_tx", 
                  "prev_commit_tx_revoked"}


(***************************************************************************)
(* Initialise channels and htlc with a balance and ready state             *)
(***************************************************************************)
Init == 
    /\ channel_balances = [c \in Channel \X ChannelId |-> CHOOSE b \in InitialBalance: TRUE]
    /\ htlc_balances = [c \in Channel \X ChannelId |-> 0]
    /\ htlc_states = [c \in Channel \X ChannelId |-> "ready"]

TypeInvariant ==
    \* channel balance on the sender side. Balance on c notes outstanding htlc balance for m.                                  
    /\ channel_balances \in [Channel \X ChannelId -> InitialBalance]
    \* outstanding htlc balance on receiver side. Balance on c notes outstanding htlc balance for n    
    /\ htlc_balances \in [Channel \X ChannelId -> InitialBalance]
    \* channels htlc state       
    /\ htlc_states \in [Channel \X ChannelId -> update_states]          
    
-----------------------------------------------------------------------------

(***************************************************************************)
(* When invoked on channel <<a, b>>.  The commit transaction of b is       *)
(* affected.  We simply track the outstanding htlc balance and don't model *)
(* the entire commit transaction.                                          *)
(***************************************************************************)
update_add_htlc(c, amount) ==
     \* Commit tx state can be in any of these states
    /\ htlc_states[c] \in {"ready", "in_latest_commit_tx"}
     \* Update only if amount is more than zero
    /\ amount > 0
     \* Update only if there is sufficient balance
    /\ channel_balances[c] - amount >= 0
     \* Change htlc balance in the commit transaction
    /\ htlc_balances' = [htlc_balances EXCEPT ![c] = @ + amount]
     \* Change channel balance in the commit transaction for sender        
    /\ channel_balances' = [channel_balances EXCEPT ![c] = @ - amount]
     \* Keep receiving updates until sender has exhausted channel sender's balance
    /\ htlc_states' = [htlc_states EXCEPT ![c] = "in_latest_commit_tx"]

-----------------------------------------------------------------------------

Next ==
    \/ \exists c \in Channel \X ChannelId, a \in InitialBalance:
            /\ update_add_htlc(c, a)
        
Spec == 
    /\ Init
    /\ [][Next]_<<vars>>
=============================================================================

