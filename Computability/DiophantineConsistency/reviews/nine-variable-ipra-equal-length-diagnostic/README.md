# Equal-length source-root diagnostic for nine-variable peer stages

An additional guarded overlay at `/tmp/nine-ipra-guarded-verify-20261102-a`
replayed stages 1–6 successfully. Its root has the same string length as the
historical author root `/tmp/nine-ipra-guarded-author-20261102-h`. Both
runner ledger checks passed; the replay uses the same pinned sources,
historical parent, and author's registered warning baselines. The six source
hashes and normalized complete compiler outputs agree.

In stages 2 and 6, the author and diagnostic object hashes differ. Their
objects have equal lengths and the corresponding source pathname occurs
exactly once; replacing the author's entire equal-length pathname with the
diagnostic pathname makes **every byte** of the author object equal to the
diagnostic object. Stages 1, 3, 4 and 5 have identical object bytes without
replacement. Direct-input hashes agree for all stages except stage 4, which
imports the two different stage-2 objects. In particular the author and
diagnostic stage-6 direct-input hashes all agree.

This is evidence that the unequal-length [peer stage-6 discrepancy](../nine-variable-ipra-peer-stages-six-ten/README.md)
is associated with its different source-path layout. It does not formally
explain the 553 aligned-word differences in those two original objects,
verify Lean serialization semantics, or justify treating their bytes as
identical. It is also not an independently re-established historical
transitive project, package or dynamic ancestry, a full 104-stage paired
replay, or an endpoint proof.

[`audit.py`](audit.py) checks the complete object bytes, source and warning
logs, and records every differing direct input hash. [`capture.py`](capture.py)
retains source snapshots, receipts, dependency listings, logs, audit output
and terminal receipt in [`observations`](observations/). The live `/tmp`
overlays and inherited providers are needed to rerun it. Filesystem guards
are checked at sampled boundaries, not continuously.
