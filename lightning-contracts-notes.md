
# Notes on Liveness

## Supersede commitment (No fairness)

Protocol allows for a behaviour where a commitment tx is never
created.

## Broadcast commitment (No fairness)

Protocol allows for a behaviour where a commitment tx is never
broadcasted to the network.

That is, the channel remains open forever. Therefore, we don't include
a liveness property for publishing a commitment tx.


## Broadcast Breach Remedy (Weak fairness)

This is the action that can be defined to be have weak fairness. The
reason is the offending transaction should be in mempool and this BR
transaction should get a chance. However, this behaviour is not part
of LN contracts per se, but of the environment (bitcoin). However, we
constraint the env to behave as expected and then we include WF for
this action in the liveness properties of the LN Contracts spec.

## Confirm mempool tx (No fairness)

This is again the action that the environment takes, so we don't need
to state it has weak fairness. The chain might stop, for example.

# Questions

## Creating commitment transactions

1. In the TLA+ spec we allow parties to create new commitment
   transactions even after the funding transaction has been
   spent. There is no way to enforce a different behaviour, so we
   allow it to test what it means for our supported properties.


## Breach remedy transactions

1. We use the BR transaction corresponding to the offending
   transaction. I don't know if this is required. Can we always
   broadcast a single breach transaction since we pay the entire
   channel balance to the party broadcasting a BR tx.

## TLA+ question

1. Channels can infinitely ping-pong payments and go on
   forever. Currently we cap commitment tx generation by putting an
   artificial upper bound on number of CTs we allow. Is there a better
   way to do this?
