------------------------ MODULE BitcoinTransactions ------------------------

(***************************************************************************)
(* This spec captures the actions and states of bitcoin transactions in    *)
(* the context of the bitcoin blockchain.  These actions will be used by   *)
(* the LN Contracts spec and other layer two contract specifications.      *)
(*                                                                         *)
(* The focus of this module is to provide:                                 *)
(*                                                                         *)
(* 1.  Way to generate transactions that accept input and generate outputs *)
(*                                                                         *)
(* 2.  Confirm transactions so that outputs can be spent.                  *)
(*                                                                         *)
(* 3.  Most importantly - provide a way to verify spend conditions without *)
(* building the entire cryptography machinery.  This enables spec authors  *)
(* to focus on what the conditions achieve instead of how those conditions *)
(* are achieved.                                                           *)
(*                                                                         *)
(* Goal A: Move environment / bitcoin transaction actions and variables    *)
(* from Contracts to here                                                  *)
(***************************************************************************)

EXTENDS Sequences,
        Integers,
        TLC,
        SequencesExt,
        FiniteSetsExt

(***************************************************************************)
(* Define constants so that we can define finite sets for inputs, outputs  *)
(* and txids etc.                                                          *)
(***************************************************************************)        
CONSTANTS CSV,          \* Set of CSV values
          VOUT,         \* Set of vout values
          TXID,         \* Set of transaction ids
          AMOUNT,       \* Set of amounts that can be used
          PARTY,        \* Parties participating in the L2 protocol
          KEY,          \* Set of keys for each party used
                        \* in the L2 protocol
          HASH          \* Set of all hash preimages

SighashFlag == {"all", "none", "single", "anyonecanpay"}

(***************************************************************************)
(* Set of output types supported for building contracts.                   *)
(*                                                                         *)
(* Each output type will have to provide a means to verify an input trying *)
(* to spend it.                                                            *)
(***************************************************************************)
\* OutputTypes == {"p2wkh", "multisig", "multisig_with_csv", "hash_lock"}
OutputTypes == {"p2wkh", "multisig", "multisig_with_csv"}

NoCSV == CHOOSE c: c \notin CSV
MaxCSV == CHOOSE c \in CSV: \A y \in CSV: c >= y
NoHash == CHOOSE h: h \notin HASH
NoTxid == -1
NoSpendHeight == -1

\* All keys available for use by the parties
Keys == PARTY \X KEY

Input == [
    txid: TXID,
    index: VOUT,
    sighash_flag: SighashFlag,      \* Parts of transactions covered by signature
    signed_by: Seq(Keys),            \* One or more keys that have signed this input
    hash_preimage: HASH \cup {NoHash}
]

Output == [
    index: VOUT,
    type: OutputTypes,
    keys: Seq(Keys),             \* Sig from these keys is required to spend
    csv: CSV \cup {NoCSV},      \* The CSV should have expired before spend
    hash: HASH \cup {NoHash},   \* Pre-image required to spend
    amount: AMOUNT
]

-----------------------------------------------------------------------------

VARIABLES
    chain_height,
    transactions,
    mempool,
    published
-----------------------------------------------------------------------------

CreateP2WKHOutput(keys, amount) == [
    index |-> 1,
    type |-> "p2wkh",
    keys |-> keys,
    csv |-> NoCSV,
    hash |-> NoHash,
    amount |-> amount
]

CreateP2WKHWithCSVOutput(keys, amount) == [
    index |-> 1,
    type |-> "p2wkh",
    keys |-> keys,
    csv |-> MaxCSV,
    hash |-> NoHash,
    amount |-> amount
]

CreateMultisigOutput(keys, amount) == [
    index |-> 1,
    type |-> "multisig",
    keys |-> keys,
    csv |-> NoCSV,
    hash |-> NoHash,
    amount |-> amount
]

CreateMultisigWithCSVOutput(keys, amount) == [
    index |-> 1,
    type |-> "multisig_with_csv",
    keys |-> keys,
    csv |-> MaxCSV,
    hash |-> NoHash,
    amount |-> amount
]

(***************************************************************************)
(* Create a transaction spending the given output/id, and spendable by the *)
(* given key.                                                              *)
(***************************************************************************)
CreateP2WKHTx(spending_output, output_key, amount) == [
    inputs |-> <<[txid |-> spending_output[1],
                index |-> spending_output[2],
                sighash_flag |-> "all",
                signed_by |-> transactions[spending_output[1]].outputs[spending_output[2]].keys,
                hash_preimage |-> NoHash]>>,
    outputs |-> <<CreateP2WKHOutput(output_key, amount)>>
]

(***************************************************************************)
(* Create a transaction spending the given output/id, and spendable by as  *)
(* a multisig of the given keys.                                           *)
(***************************************************************************)
CreateMultisigTx(spending_output, output_keys, amount) == [
    inputs |-> <<[txid |-> spending_output[1],
                index |-> spending_output[2],
                sighash_flag |-> "all",
                signed_by |-> transactions[spending_output[1]].outputs[spending_output[2]].keys,
                hash_preimage |-> NoHash]>>,
    outputs |-> <<CreateMultisigOutput(output_keys, amount)>>
]

CreateUnsignedMultisigTx(spending_output, output_keys, amount) == [
    inputs |-> <<[txid |-> spending_output[1],
                index |-> spending_output[2],
                sighash_flag |-> "all",
                signed_by |-> <<>>,
                hash_preimage |-> NoHash]>>,
    outputs |-> <<CreateMultisigOutput(output_keys, amount)>>
]

CreateMultisigWithCSVTx(spending_output, output_keys, amount) == [
    inputs |-> <<[txid |-> spending_output[1],
                index |-> spending_output[2],
                sighash_flag |-> "all",
                signed_by |-> transactions[spending_output[1]].outputs[spending_output[2]].keys,
                hash_preimage |-> NoHash]>>,
    outputs |-> <<CreateMultisigWithCSVOutput(output_keys, amount)>>
]

(***************************************************************************)
(* Choose keys to use in outputs.  It is used by AddSpendTxToMempool.      *)
(*                                                                         *)
(* We expect both this expression and the AddSpendTxToMempool action to be *)
(* provided by the layer 2 protocol spec.                                  *)
(***************************************************************************)
ChooseOutputKeys(output_type) ==
    IF output_type = "p2wkh"
    THEN SetToSeq(CHOOSE k \in kSubset(1, Keys): TRUE)
    ELSE SetToSeq(CHOOSE k \in kSubset(2, Keys): TRUE)

(***************************************************************************)
(* Return TRUE if the given output uses a key for the provided party       *)
(***************************************************************************)
OutputOwnedByParty(o, p) ==
    p \in {k[1]: k \in ToSet(transactions[o[1]].outputs[o[2]].keys)}

ConfirmedTransactions ==
    {p \in DOMAIN transactions: published[p] # NoSpendHeight}

AllOutputs ==
    UNION {{txid} \X {o.index: o \in ToSet(transactions[txid].outputs)}: txid \in ConfirmedTransactions}

SpentOutputs ==
    {<<i.txid, i.index>> : i \in 
            UNION {ToSet(transactions[txid].inputs) : txid \in ConfirmedTransactions}
    }

UnspentOutputs == AllOutputs \ SpentOutputs

-----------------------------------------------------------------------------

(***************************************************************************)
(* Add a coinbase tx spendable with a pk.  No verification is required     *)
(* here as no prevout is being spent.                                      *)
(***************************************************************************)
AddP2WKHCoinbaseToMempool(id, keys, amount) ==
    /\ id \notin mempool
    /\ published[id] = NoSpendHeight
    /\ transactions' = [transactions EXCEPT ![id] = [inputs |-> <<>>,
                            outputs |-> <<CreateP2WKHOutput(keys, amount)>>]]
    /\ mempool' = mempool \cup {id}
    /\ UNCHANGED <<chain_height, published>>

AddTxidToMempool(id) ==
    /\ id \notin mempool
    /\ published[id] = NoSpendHeight
    /\ mempool' = mempool \cup {id}
    /\ UNCHANGED <<chain_height, published>>

(***************************************************************************)
(* Add a coinbase tx with a multisig output spendable by signature from    *)
(* all keys.                                                               *)
(*                                                                         *)
(* We don't do threshold signatures for simplicity.                        *)
(***************************************************************************)
AddMultisigCoinbaseToMempool(id, keys, amount) ==
    /\ id \notin mempool
    /\ published[id] = NoSpendHeight
    /\ transactions' = [transactions EXCEPT ![id] = [inputs |-> <<>>,
                            outputs |-> <<CreateMultisigOutput(keys, amount)>>]]
    /\ mempool' = mempool \cup {id}
    /\ UNCHANGED <<chain_height, published>>

(***************************************************************************)
(* Confirm transaction from mempool.                                       *)
(***************************************************************************)
ConfirmMempoolTx(id) ==
    /\ id \in mempool
    /\ published[id] = NoSpendHeight
    /\ LET tx == transactions[id]
       IN
        /\ chain_height' = chain_height + 1 \* Each tx is in it's own block
        /\ published' = [published EXCEPT  ![id] = chain_height']
        /\ mempool' = mempool \ {id}
    /\ UNCHANGED <<transactions>>

(***************************************************************************)
(* Add a new transaction to mempool.                                       *)
(*                                                                         *)
(* The transaction is created and added to mempool.                        *)
(*                                                                         *)
(* The transaction is constructed such that it is a valid transaction.     *)
(*                                                                         *)
(* `input_type` specifies the type of published output to select to spend. *)
(*                                                                         *)
(* `output_type' specifies the type of new output to create.               *)
(***************************************************************************)
AddSpendTxToMempool(id, amount, input_type, output_type) ==
    \E spending_output \in UnspentOutputs:
        /\ id \notin mempool
        /\ transactions[spending_output[1]].outputs[spending_output[2]].type = input_type
        /\ transactions' = [transactions EXCEPT ![id] =
                CASE (output_type = "p2wkh") ->
                        CreateP2WKHTx(spending_output,
                            ChooseOutputKeys(output_type), amount)
                   [](output_type = "multisig") ->
                        CreateMultisigTx(spending_output,
                            ChooseOutputKeys(output_type), amount)
                   [](output_type = "multisig_with_csv") ->
                        CreateMultisigWithCSVTx(spending_output,
                            ChooseOutputKeys(output_type), amount)
           ]
        /\ mempool' = mempool \cup {id}
        /\ UNCHANGED <<chain_height, published>>

=============================================================================
