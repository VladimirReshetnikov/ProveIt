# Integration proposal and review boundary

Reference revision: `8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`.

## Intended mathematical change

For a fixed nonnegative occurrence matrix, full positive singleton cancellation is equivalent to private-column peeling. The current minimum-fill heuristic has the same full-success decisions and uses no fill on successful runs. The proposal saves repeated scanning and permits sparse source-based verification; it does not add accepted geometric cases.

The canonical stopping residual excludes full elimination in this calculus. It is neither a knot obstruction nor a maximum partial schedule. Existing `INCONCLUSIVE` semantics must be preserved.

## Proposed source changes

The applicator changes only completion-oriented fallback calls in:

1. `Topology/UnknotRecognition/fast/fastunknot/core_handlebody.py`
2. `Topology/UnknotRecognition/fast/fastunknot/bundle_boundary_kernel.py`

It retains the current row-leaf path and the square early refusal. It does **not** replace or remove the general `capped_cancellation_plan` function. Consumers interested in partial cancellations may continue to use it.

It also adds an independent private-column fast path to `core_handlebody_verify.py`, after that checker has reconstructed the matrix from source charts. Private full schedules skip dense replay. Every other schedule retains the legacy fallback, so the optimization does not silently narrow the certificate language.

Two files are added: `column_cancellation.py` (the producer) and `column_cancellation_verify.py` (a checker with no producer import). Core certificates retain the existing schema and `capped` method label. The whole-cut boundary verifier is **unchanged**; it needs a separate source-aware review before a complete whole-cut query can be credited with the sparse verification improvement.

## Application

On a clean, reviewed, LF-preserving checkout of the pinned files:

```sh
python integration/apply.py /path/to/ProveIt
python integration/apply.py /path/to/ProveIt --write
```

The first command is a dry run. The second writes only after all source pins and patch anchors pass, retaining `.before-column-cancellation` backups. The writes are not a multi-file transactional filesystem operation; use a clean worktree and review the diff.

The applicator requires exact Git blob identities. It intentionally refuses a newer source revision, altered line endings, ambiguous anchors, or existing new modules. Port and review changes rather than bypassing the pin. Source hashes and review scope are recorded in `SOURCE_AUDIT.json`.

## What was actually tested

The standalone kernels, independent verifier, exhaustive matrix oracles, and proposed producer composition were executed. The independent core-verifier helper was compared on all 729 ternary 2-by-3 matrices. Patch transformations were checked on explicit target-text fixtures and compiled for syntax. Git hashing was checked on a known empty-blob identity.

**Not run:** application to the actual full checkout, the production test suite, source-geometric reconstruction benchmarks, and full knot recognition. The reference native planner is a transcription of the two inspected function bodies, not a byte-identical full source snapshot. The archive must not be integrated as though those broader tests had passed.

## Required review before enabling

Compare this manuscript with incoming stopping-core and saturated-bundle-cancellation manuscripts whose archive bodies were inaccessible here. Check all full-success and refusal decisions on maintained source-certified cuts. Run old and new source-based verifiers on the same schedules and include old non-private certificates. Measure source preparation, scheduling, verification, serialization and census together. Audit stats consumers for any assumptions about planner-specific counters or ordering of partial residual rows.

## Geometric trust boundary

Only raw unsigned cocore intersections reconstructed from authenticated charts may feed the topological consumer. Do not substitute signed exponent sums. A positive matrix result does not supply a boundary-pattern exporter. A deferred two-handle remains present even when its numerical row becomes zero. Do not apply a terminal genus census while unresolved deferred two-handles remain.
