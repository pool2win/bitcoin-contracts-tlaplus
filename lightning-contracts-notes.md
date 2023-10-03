
# Notes on Liveness

## Commitment tx

Protocol allows for a behaviour where a commitment tx is never
published. That is, the channel remains open forever. Therefore, we
don't include a liveness property for publishing a commitment tx.


## Breach Remedy tx

This definitely has a liveness requirement and we include it in the
spec.


# Questions

## Creating commitment transactions

1. In the TLA+ spec we allow parties to create new commitmentment
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
