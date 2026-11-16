# Model-valued source/scheduler fetch prefix

`PA194SchedulerFetchModel.fetchPrefix` proves a concrete part of the actual encoded controller/scheduler correspondence in every structure satisfying PRA and the separately stated IΣ₁ model assumption. Assume the scheduler's N and L fields match source registers 0 and 8 and the source scratch register X (register 6) is zero. The theorem supplies a model-valued number of actual controller steps taking source site 25 to site 34 and a resulting register file such that:

- source register L equals the actual packed scheduler's `fetchSeed` value;
- source register N equals the N field of the actual next packed scheduler state;
- X is again zero, all source registers other than N and L are preserved, and the full controller-file tail is preserved.

Both L branches are covered. For positive L the controller takes two steps. For L=0, the result uses Σ₁-inductive drain and restore invariants for arbitrary, possibly nonstandard model values of N. These prove the source run executes `4N+1` and `3N+2` steps in the two loops, respectively, after the initial branch. The matching hypotheses concern only the scheduler/source N and L fields; they do not assume the desired fetch conclusion.

This is a Lean semantic model theorem, not a native iPRA derivation. It stops at site 34, before the remaining command decode and dispatch, and does not prove the scheduler's other fields, full scheduler/controller synchronization, physical-machine simulation, or a consistency implication.

The twelve new source modules, in dependency order, are `PA194SchedulerFetchPositive.lean`, `PA194SchedulerPackedFetchPositive.lean`, `PA194SchedulerFetchFresh.lean`, `PA194SourceFetchLoop.lean`, `PA194ControllerRunAdd.lean`, `PA194SourceDrainInvariant.lean`, `PA194SourceDrainModel.lean`, `PA194SourceFetchRestoreLoop.lean`, `PA194SourceRestoreInvariant.lean`, `PA194SourceRestoreModel.lean`, `PA194SourceFetchModel.lean`, and `PA194SchedulerFetchModel.lean`.

The independent common-source audit passed with:

```
/dev/shm/pa194-scheduler-controller/check-fetch-coherent-v2.sh "$PWD" /dev/shm/pa194-scheduler-controller /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-termgraph/DiophantineConsistency /dev/shm/pa194-fetch-coherent-full-v2
```

The shell wrapper pins the twelve new source hashes. Its Python helper rebuilds the 270-module standalone machine/controller/scheduler import closure from source in a fresh single output, regenerates and pins the source tree, records source hashes in `source-closure.json`, rechecks them at the end, and audits final axiom reports. It rejects machine-specific fallback objects in the two general foundation overlays and Lake search roots. The graph fallback is exposed only as the `DiophantineConsistency` namespace; no root-level machine objects from `/dev/shm/pa194-termgraph` enter `LEAN_PATH`. The audit runs no git commands. The independent run exited successfully; a second full rebuild from repository sources also passed with log `/tmp/pa194-fetch-coherent-repo.log`.

The graph namespace is an existing prebuilt overlay. It has six real, pinned `.olean` objects and 577 other entries symlinked into the project foundation; the wrapper checks the six-object set, their hashes, and that every symlink resolves inside that project namespace. The retained objects and SHA-256 hashes are:

```
PRAHistoryResultGraph.olean        2654808e5cfba0266f38ce2ddad33987635e8e06c3934cc131eb2a475bc1eeae
PRAHistoryTrace.olean              4b3ea00b4fbf5790008bddc61a69d2b7bdf84551e67084219014b57bd6402db2
PRAHistoryIterator.olean           b359da5684d709684b25fcd7c7073804a91044fc54ae0f2bfc9b44a7b1844583
PRAHistorySingletonSequence.olean  e976a9cc5de9e9ca257f78e16ea444a32684ecc3cb74f4c8f0bef7fabbb1ce40
PRAHistorySingletonMembership.olean 85aeb8494921b2211b7c4ca01b0fce4b5153ce0839ad6bc5e087dfdbb047c45d
PRAHistoryLengthUnique.olean       d225bca0cd681778109ef906169e7f7a0549289635c81e2a987f3cd67aab1c58
```

Their corresponding source paths are under `Computability/DiophantineConsistency/Lean/DiophantineConsistency`; the audit pins the prebuilt objects and does not independently establish that those objects were built from the present sources. The two general foundational overlays also remain prebuilt.

The first common-source attempt failed at module 21 because `PRAHistoryResultGraph.olean` was absent from the project foundation. Its log and partial fresh output remain at `/tmp/pa194-fetch-coherent-full.log` and `/dev/shm/pa194-fetch-coherent-full`. The restarted audit uses the graph namespace described above and a separate output; the first failure is not a proved scheduler/controller mismatch.

A prior independent staged replay through the complete fresh L=0 fetch passed in `/tmp/pa194-scheduler-fresh-fetch-model-replay.log`. It used overlapping prebuilt scheduler/controller prerequisite overlays, including 821 overlapping names with some differing bytes, and did not audit their full transitive compatibility; it does not include the final unified both-branch theorem. The successful common-source audits above rebuild that standalone closure together, subject to the stated graph and foundation limitations.

The full v2 common-source audit completed with exit status 0. The preserved log reports 270 of 270 modules compiled, both final axiom reports without `sorryAx`, and all source hashes unchanged. This result retains exactly the prebuilt graph namespace and foundation limitations described above.
