# Model-uniform scheduler/controller fetch components

The source controller and scheduler both use actual PR-code definitions. `PA194SchedulerFetchPositive.positiveFetchPrefix` proves over any PRA model that source L=m+1 sends the actual controller through 25→26→34, setting L to m and preserving all other logical registers and the controller tail; the scheduler's `fetchSeed` and `nextN` functions give m and N. `PA194SchedulerPackedFetchPositive.packedPositiveFetchPrefix` connects this with an actual packed scheduler state and its next-state N field, assuming the scheduler/source N and L fields match. Its packed-field proof additionally uses IΣ₁.

`PA194SchedulerFetchFresh.freshFetchPrefix` establishes the other initial branch: for L=0 the source controller moves 25→27 unchanged, while the scheduler fetch seed is N and its next-state N is N+1. This does not assert the source has finished the fresh fetch. `PA194SourceFetchLoop.drainLoop` proves one actual source-controller pass 27→28→29→30→27 for any PRA model and positive N; it decrements N, increments L and X, and preserves the remaining registers and controller-file tail. The same file gives reusable all-site instruction-step lemmas for increments, jumps, and positive decrements.

These are semantic Lean model theorems, not native iPRA derivations. They do not yet iterate the drain over a model-valued count, finish the source fetch/restore, match the scheduler's remaining packed fields, or establish a full scheduler/controller correspondence or consistency implication. No physical-machine equivalence is claimed.

The four new sources in build order are `PA194SchedulerFetchPositive.lean`, `PA194SchedulerPackedFetchPositive.lean`, `PA194SchedulerFetchFresh.lean`, and `PA194SourceFetchLoop.lean`. The replay invocation from the repository root is:

```
/dev/shm/pa194-scheduler-controller/check-scheduler-fetch-components.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-scheduler-controller /dev/shm/pa194-qf-seed-audit
```

The replay log `/tmp/pa194-scheduler-fetch-components-replay.log` records exit 0 and PASS. The checker rebuilds the source-controller suffix and five scheduler/command modules in one fresh output before the new sources and audits printed axioms for `sorryAx`. Its temporary read-only object view gives precedence to the unified controller baseline, then graph overlay, then the prebuilt scheduler overlay. These input overlays have 821 overlapping object names; some overlaps have different bytes, and the checker does not authenticate or establish compatibility of their full transitive closures. It pins selected prerequisite objects, not the entire scheduler closure. The general foundations are also prebuilt. A fully source-rebuilt common closure remains desirable before treating this as a coherent end-to-end audit.

The repository-source replay also passed using this directory for all three
source-directory arguments and the same overlapping retained overlays. It does
not remove the closure-compatibility limitation described above.
