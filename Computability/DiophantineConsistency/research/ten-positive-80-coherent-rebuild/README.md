# Draft coherent 80 symbolic iPRA replay

**SUPERSEDED:** subsequent [historical producer comparisons](../../reviews/ten-positive-80-ha87-producer-drift/README.md)
expanded the provisional affected cone to 127 modules, so this 122-stage
runner must not be launched as a repair of the current known drift. Its
retained script is historical preparation only.

**DRAFT / HOLD: do not launch `run.py` until an independent static review of
this exact script, its inputs, scope, guards, warning policy, and output
handling is complete.** No replay is claimed here.

The 122-stage plan is now **superseded**: additional historical producer
records expand the observed-drift reverse-reachable cone to at least 127
modules. The existing runner must not be launched; a new pinned plan and
runner are required.

`run-v2.py` is the replacement draft pinned to the 127-module source plan,
SHA-256 `b5d1c48634b9fb78c0c543c2523537ea71225b1dea9906d4fc5faee6efb6bc2a`.
The independent v2 review found blocking in-flight memory and diagnostic
guard defects; v2 is held and must not be launched. Its selected package input includes the current Foundation object;
the prior Foundation-object discrepancy and package-transitive ancestry
remain separate limitations.

`run-v3.py`, SHA-256
`c262d844c28fe87954cfe06d14da359d08e4d88838cb32bce025f26b072269d5`,
is a corrected, **held and unlaunched** draft for independent re-review. It
adds an 8-GiB in-flight guard, coded diagnostic detection, a recorded current
outside-object/companion baseline with stage and final rechecks, final rehashes
of all original and copied sources, an exact fixed-client receipt pin, a
planned-stage record before resource preflight, and atomic result replacement.
`check-diagnostics.py` checks seven positive and four negative diagnostic
mutations without running the rebuild; `diagnostics-v3.stdout` records its
successful result. The outside baseline records current bytes, not a proof of
their historical provenance or transitive package ancestry.

An [independent v3 prelaunch audit](../../reviews/ten-positive-80-rebuild-v3-prelaunch-independent/README.md)
has since reviewed the exact runner and proposed one coordinated guarded run.
An accepted result requires outer exit 0 and final `PASS`, followed by a
separate audit of all stages, headers and endpoint reports; a per-stage
`RETURNED` status alone is not a success receipt.

The v3 runner uses the selected 1,765-project-module closure and the
expanded source-pinned 127-module drift cone. It materializes one fresh
project union under `/tmp`, snapshots every candidate source, and rebuilds the
cone in its captured topological order. It is intended to verify source and
direct object/companion hashes before and after each stage, require the
8-GiB/two-process preflight, sample resources, reject all Lean warnings and
errors, retain stage logs and receipts, recheck the full project union and
actual serialized headers of all rebuilt objects, and inspect all four fixed
endpoint axiom reports. Any warning is currently fatal; no warning exception
is approved by this draft.

The 127-module cone is driven by observed producer-time discrepancies and is
not known to cover every historical mismatch. Even a successful replay would
leave unrebuilt historical source/object ancestry, package-transitive and
dynamic dependencies, and external JSON/PDF binding open. The symbolic K0 in
the endpoint differs from the other direct-BFS candidate coefficient; do not
transfer the result between those tuples without a separate proof.

The superseded original runner SHA-256 is
`d0b0e8beb7db9beccb2dccea73b804b3bb37a72d1bd315717c6df0f1b1ba0d03`.
Review the script itself and its pinned source-plan and closure inputs rather
than relying on this summary. A failed or interrupted attempt must retain its
observations and never overwrite another attempt.
