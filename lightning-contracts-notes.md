
# Separating Bitcoin from LN Contracts

For the work up till now, I have some more clarity on which actions
can be moved to the environment. In our case, the environment is the
bitcoin blockchain. For example, the actions like BroadcastCommitment
and ConfirmTx can be moved to be properties of the environment. This
will simplify the spec of LN contracts and will allow tackling other
layer two protocols.


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

In the TLA+ spec we disallow creating new commitment transactions if
the funding transaction is confirmed. We could allow this and check
they are never confirmed, however, there is not much value in checking
such behaviours.


## Breach remedy transactions

We use the BR transaction corresponding to the offending
transaction.
