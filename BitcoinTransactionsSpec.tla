---------------------- MODULE BitcoinTransactionsSpec ----------------------
(***************************************************************************)
(* This Spec is used to run a model against the BitcoinTransactions        *)
(* module.                                                                 *)
(*                                                                         *)
(* By moving the model and the runner here, we allow other modules like    *)
(* LNContracts to freely use BitcoinTransactions and run their own models. *)
(***************************************************************************)
EXTENDS BitcoinTransactions

-----------------------------------------------------------------------------

vars == <<chain_height, transactions, mempool, published>>

Init ==
    /\ transactions = [id \in TXID |-> [inputs |-> <<>>, outputs |-> <<>>]]
    /\ chain_height = 0
    /\ mempool = {}
    /\ published = [id \in TXID |-> NoSpendHeight]
    
TypeOK ==
    /\ transactions \in [TXID -> [inputs: Seq(Input), outputs: Seq(Output)]]
    /\ mempool \in SUBSET TXID
    /\ published \in [TXID -> Int]
    
-----------------------------------------------------------------------------

Next == 
    \/ \E k \in Keys, id \in TXID, a \in AMOUNT:
        \/ AddP2WKHCoinbaseToMempool(id, <<k>>, a)
    \/ \E keys \in Keys \X Keys, id \in TXID, amount \in AMOUNT:
        \/ AddMultisigCoinbaseToMempool(id, keys, amount)
    \/ \E id \in TXID, a \in AMOUNT, k \in Keys, input_type \in OutputTypes, output_type \in OutputTypes:
        AddSpendTxToMempool(id, <<k>>, a, input_type, output_type)
    \/  \E id \in TXID: ConfirmMempoolTx(id)

Spec == 
    /\ Init
    /\ [][Next]_<<vars>>
=============================================================================
