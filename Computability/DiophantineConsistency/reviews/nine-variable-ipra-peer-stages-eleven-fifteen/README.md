# Nine-variable peer replay: stages 11–15

The guarded peer completed stages 11–15. Both the peer and historical author
ledger checks passed; each stage has matching source hashes and complete
compiler logs after source-path normalization. The peer reused the author's
source-bound warning baselines. Stages 13–15 produced byte-identical objects.
Stages 11 and 12 produced different object hashes: this is not an exact
paired byte match.

Stages 11 and 12 have equal author/peer object sizes. In each, the differing
source pathname occurs exactly once and has an equally sized NUL-padded
region. Replacing the three path-length fields and that padded source-path
region makes the complete author bytes equal to the peer bytes; the audit
checks the entire object, not a sample. This is a byte-level observation,
not a proof of Lean's object format or semantic interchangeability. Stage 12
directly imports the different stage-11 objects. Stage 13 directly imports
different stage-12 and stage-7 objects, despite its own matching output.
Stages 14 and 15 have matching direct-input hashes and matching output hashes.

[`audit.py`](audit.py) verifies those observations and raw direct-input hash
differences, while [`capture.py`](capture.py) retains exact receipts, source
snapshots, compiler and dependency logs, audit output and terminal status in
[`observations`](observations/). Repeating the audit requires the live
historical and peer `/tmp` overlays. Guards are sampled; historical transitive
project, package and dynamic ancestry remains inherited. The first fifteen
stages do not establish an endpoint replay or a full dependency-closure audit.
