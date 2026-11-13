# Nine-variable CURRENT2011 endpoint: author observations

The single-author replay accepted stages 75–81, ending with
`IPRANineCurrent` and `IPRANineChecks`. The endpoint asserts native,
standard and equality-only iPRA equivalences for the **CURRENT2011-based**
nine-variable expression. The checks module printed all 15 expected reports;
their only Lean metatheory axioms were `propext`, `Classical.choice`, and
`Quot.sound`. These are not added object-theory axioms.

`ShortSystem` and `ModelCarrierScaled` were retried against source-bound
complete warning baselines. Retained receipts, source snapshots, dependency
listings, logs, rejected attempts and baselines are under `author/`; output
objects remain in the live temporary overlay. `capture.py` checked their hashes
when retaining the packet.

This is a point-in-time author observation, not an independent artifact audit,
paired replay or authenticated transitive closure. It does not establish the
separate `ExplicitZFC` nine-variable endpoint or interpret document bytes.
