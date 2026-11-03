# Draft coherent 80 symbolic iPRA replay

**DRAFT / HOLD: do not launch `run.py` until an independent static review of
this exact script, its inputs, scope, guards, warning policy, and output
handling is complete.** No replay is claimed here.

The proposed runner uses the selected 1,765-project-module closure and the
expanded source-pinned 122-module drift cone. It materializes one fresh
project union under `/tmp`, snapshots every candidate source, and rebuilds the
cone in its captured topological order. It is intended to verify source and
direct object/companion hashes before and after each stage, require the
8-GiB/two-process preflight, sample resources, reject all Lean warnings and
errors, retain stage logs and receipts, recheck the full project union and
actual serialized headers of all rebuilt objects, and inspect all four fixed
endpoint axiom reports. Any warning is currently fatal; no warning exception
is approved by this draft.

The 122-module cone is driven by observed producer-time discrepancies and is
not known to cover every historical mismatch. Even a successful replay would
leave unrebuilt historical source/object ancestry, package-transitive and
dynamic dependencies, and external JSON/PDF binding open. The symbolic K0 in
the endpoint differs from the other direct-BFS candidate coefficient; do not
transfer the result between those tuples without a separate proof.

The draft runner SHA-256 is
`d0b0e8beb7db9beccb2dccea73b804b3bb37a72d1bd315717c6df0f1b1ba0d03`.
Review the script itself and its pinned source-plan and closure inputs rather
than relying on this summary. A failed or interrupted attempt must retain its
observations and never overwrite another attempt.
