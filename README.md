
# Bitcoin layer two contracts and communication protocols in TLA+


## Problem

Layer 2 contracts for bitcoin are hard to reason about. Capturing
complex protocols in TLA+ helps us think about the various edge and
corner cases without dealing with complicated programming language
issues.

## Goals

There are two simple goals of this repo:

1. Provide basis to capture layer 2 contracts in TLA+.
2. Also exercise the communication protocols required to implement
   layer 2 contracts - this can have some dependencies on 1.

To develop the above two we start with lightning network. By using the
above two to capture behaviours of LN contracts we can state the
project's goals have been achieved.


## Progress

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
