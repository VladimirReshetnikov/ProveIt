# Evidence and trust boundaries

These receipts record work actually executed in this research session.
Original execution paths, Python versions, timings and argv strings remain
provenance; moving a file does not retroactively change the execution record.
Input byte hashes identify the corresponding delivered tables.

Primary receipts:

- `candidate239_target106_universal.json` and `_cases.json`: fresh complete
  invocation of the unchanged symbolic engine on the primary old-label table.
- `guard169_universal.json`, `guard169_visits.json`, `guard169_cases.json`:
  fresh complete invocation of the final portable guard instrument. The
  instrument hash identifies its exact executed bytes.
- `guarded_fold239_certificate.json`: exact finite-footprint block/invariant
  proof and every checkpoint of the finite blank prefix.
- `candidate239_target106_boot.json`: separately written sparse and dense
  literal startup simulations, including the complete one-cell support.
- `independent_source_bridge.json`: final portable source parser run on the
  exact pinned Lean row/lookup/wrapper definitions.
- `UNIVERSAL239_AUDIT.md`: mathematical review of the induction rules,
  clean-pointer bridge, startup and consistency composition.
- `package_quick_replay.json`: default replay of the assembled portable package.

`REPORT_REVIEW.json` records the hashes of a reviewed manuscript version.
Its suggested corrections to the retained-row count, same-header-distance
wording and equality-free EPSC matrix convention were applied afterward.
It also independently checked all 478 displayed table entries against the
canonical machine. The final PDF was separately rendered and visually inspected.

The runtime driver uses assertions as proof obligations and rejects optimized
Python execution. Its successful symbolic derivations quantify arbitrary
natural parameters and finite spare lists. Discovery profiles and the finite
frontend regressions do not have this scope.

The independent literal block checker and startup-clock census are under
`../research/source_compression/`. They have independent implementations.
The full runtime driver there uses the same inherited induction engine;
its separate invocation is not an independent universal verifier design.

The 240-state source-equivalence and consistency proofs are inherited from
the pinned repository. Source snapshots and archived status descriptions are
in `../reference/`; they were inspected, not rebuilt in Lean during this task.
No receipt here is a proof of unconditional nonhalting or a consistency decision.
