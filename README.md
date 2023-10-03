
** Read [Notes on lighting contracts](./lightning-contracts-notes.md) **

# Bitcoin layer two contracts and communication protocols in TLA+


## Problem

Layer 2 contracts for bitcoin are hard to reason about. Often times it
comes down to writing contracts in code and then running
simulations. However, simulations are expensive to write and it is
even harder to cover all the corner cases.

## Goals

Capture L2 protocols in TLA+ to helps us think about the the
behaviours these contracts support, as well as explore corner cases
without dealing with complicated programming language issues.

There are two simple goals of this repo:

1. Provide basis to capture layer 2 contracts in TLA+.
2. Exercise the communication protocols required to implement layer 2
   contracts - this can have some dependencies on 1.

To develop the above two we start with lightning network. By using the
above two to capture behaviours of LN contracts we can state the
project's goals have been achieved.


## Progress

#### October 2023

#### Lightning contracts

Add even the initial commitment transactions, offending and breach
remedy transactions makes the behaviour of these transactions
clear. This was especially made much clearer when adding liveness
properties. I am capturing notes on lightning contracts
[here](lightning-contracts-notes.md).

### September 2023

#### HTLC

The first protocol I am interested in capturing is the HTLC forwarding
protocol as specified in [Bolt #2 section on forwarding
HTLC](https://github.com/lightning/bolts/blob/master/02-peer-protocol.md#forwarding-htlcs)

You can see the initial HTLC protocol in [htlc.pdf](./htlc.pdf). Note,
the spec needs some changes to move the focus from HTLC to commitment
transaction instead. I am parking this for the moment and switching to
work on specifying L2 contracts - we need this to make the project a
success.

#### Bitcoin contracts

This is a challenging goal, and the initial design captures the
behaviour of a bitcoin transaction. So the spec is for a bitcoin
transaction - that is the system we spec. The environment is made up
of keys, signatures, UTXO set, chain height and spend conditions that
can attached to transactions.

A transaction can thus be created and acted up by the various actors
in the environment and the transaction can then move from state to
state - specifying it's behaviour. L2 protocol authors will then write
new spend conditions and be able to check if the transaction behaviour
support the properties the want from the protocol.
