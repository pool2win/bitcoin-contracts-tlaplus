--------------------- MODULE LNContracsUsingBitcoinTransactions ------------

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
        FiniteSets,
        BitcoinTransactions

CONSTANTS
    InitialBalance   \* Initial balances for alice and bob
    
VARIABLES
    commitment_txs,         \* Commitment txs held by each party. Not yet broadcast.
    breach_remedy_txs       \* BR txs held by each party. Not yet broadcast.

-----------------------------------------------------------------------------

SeqToSet(s) == {s[i] : i \in DOMAIN s}

-----------------------------------------------------------------------------

(***************************************************************************)
(* Current channel contracts only ever have two parties                    *)
(***************************************************************************)
Party == {"alice", "bob"}
-----------------------------------------------------------------------------

vars == <<chain_height, transactions, mempool, published,
           commitment_txs, breach_remedy_txs>>

Init ==
    /\ transactions = [id \in TXID |-> [inputs |-> <<>>, outputs |-> <<>>]]
    /\ commitment_txs = [p \in Party |-> <<>> ]
    /\ breach_remedy_txs = [p \in Party |-> <<>> ]
    /\ chain_height = 0
    /\ mempool = {}
    /\ published = [id \in TXID |-> NoSpendHeight]
    
TypeOK ==
    /\ transactions \in [TXID -> [inputs: Seq(Input), outputs: Seq(Output)]]
    /\ commitment_txs \in [Party -> Seq(TXID) ]
    /\ breach_remedy_txs \in [Party -> Seq(TXID) ]
    /\ mempool \in SUBSET TXID
    /\ published \in [TXID -> Int]
    
    ChooseKey(k) == CHOOSE e \in KEY: e # k
-----------------------------------------------------------------------------

CreateFundingTx(id, keys, amount) ==
    /\ AddMultisigCoinbaseToMempool(id, keys, amount)
    /\ UNCHANGED <<commitment_txs, breach_remedy_txs>>

ConfirmTx(id) ==
    /\ ConfirmMempoolTx(id)
    /\ UNCHANGED <<commitment_txs, breach_remedy_txs>>
    
-----------------------------------------------------------------------------

Next ==
    \/ \E keys \in KEY \X KEY, id \in TXID, amount \in AMOUNT:
        \/ CreateFundingTx(id, keys, amount)
    \/ \E id \in TXID: ConfirmTx(id)

Spec == 
    /\ Init
    /\ [][Next]_<<vars>>

=============================================================================
