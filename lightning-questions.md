
* Creating commitment transactions

1. In the TLA+ spec we allow parties to create new commitmentment
   transactions even after the funding transaction has been
   spent. There is no way to enforce a different behaviour, so we
   allow it to test what it means for our supported properties.


* Breach remedy transactions

1. We use the BR transaction corresponding to the offending
   transaction. I don't know if this is required. We could just always
   broadcast a single breach transaction.

* TLA+ question

1. Channels can infinitely ping-pong payments and go on
   forever. Currently we cap commitment tx generation by putting an
   artificial upper bound on number of CTs we allow. Is there a better
   way to do this?
