---------------------- MODULE BitcoinTransactionsSpec ----------------------
(***************************************************************************)
(* This Spec is used to run a model against the BitcoinTransactions        *)
(* module.                                                                 *)
(*                                                                         *)
(* By moving the model and the runner here, we allow other modules like    *)
(* LNContracts to freely use BitcoinTransactions to add models, Init       *)
(* conditions etc.                                                         *)
(***************************************************************************)
EXTENDS BitcoinTransactions

vars == <<chain_height, transactions, mempool, published>>

Init ==
    /\ transactions = [id \in TXID |-> [inputs |-> <<>>, outputs |-> <<>>]]
    /\ chain_height = 0
    /\ mempool = {}
    /\ published = {}
    
TypeOK ==
    /\ transactions \in [TXID -> [inputs: Seq(Input), outputs: Seq(Output)]]
    /\ mempool \in SUBSET TXID
    /\ published \in SUBSET TXID
    
-----------------------------------------------------------------------------

Next == 
    \/ \E k \in KEY, id \in TXID, a \in AMOUNT: 
        \/ AddP2WKHCoinbaseToMempool(id, k, a)
    \/ \E keys \in KEY \X KEY, id \in TXID, amount \in AMOUNT:
        \/ AddMultisigCoinbaseToMempool(id, keys, amount)
    \/ \E id \in TXID, a \in AMOUNT, k \in KEY, input_type \in OutputTypes, output_type \in OutputTypes:
        AddSpendTxToMempool(id, k, a, input_type, output_type)
    \/ ConfirmCoinbaseMempoolTx

Spec == 
    /\ Init
    /\ [][Next]_<<vars>>
=============================================================================
