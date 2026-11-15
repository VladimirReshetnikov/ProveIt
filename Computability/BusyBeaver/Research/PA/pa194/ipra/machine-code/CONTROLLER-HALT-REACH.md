# Actual controller: eventual halt iff reaching site 10

`PA194ControllerHaltReach.reachesHaltIffSite10` concerns the actual encoded source-controller run in every structure satisfying both PRA and the separately stated IΣ₁ model assumption used by the iteration and induction lemmas. From any initial controller state whose PC is below 3,673, it proves that the run reaches halted sentinel 3,674 at some model time if and only if it reaches source site 10 at some model time. Those times may be nonstandard.

The forward direction is strengthened by `haltAfterSite10`: a site-10 visit occurs strictly before any time at which the run is halted. The proof handles the malformed sentinel 3,673 as a separate absorbing state, so it does not assume the source program is fully resolved. Its single-step characterization depends on the separately kernel-checked unique halt source leaf and actual source-controller selector.

This is a semantic Lean model theorem, not a native iPRA derivation. It does not identify the scheduler's hit condition with the controller run or establish source-to-physical synchronization, so it does not prove a machine/consistency implication.

The checker `check-controller-halt-reach.sh` extends `check-controller-halt-characterization.sh` with the additional source `PA194ControllerHaltReach.lean` and audits its four theorem axiom reports. Invoke from the repository root with:

```
/dev/shm/pa194-source-haltbridge/check-controller-halt-reach.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-source-haltbridge
```

The four new sources in build order are `PA194SourceHaltUnique.lean`, `PA194ControllerHaltCharacterization.lean`, `PA194ControllerHaltRun.lean`, and `PA194ControllerHaltReach.lean`. The checker regenerates and rebuilds the pinned source tree/program and unique halt leaf in a common fresh output with the controller suffix and these sources; it also checks the literal table hash and axiom reports. The earlier unified machine baseline, graph overlay, and foundations remain prebuilt, and selected hashes do not authenticate their entire transitive closure. Regenerating the source tree and pinning the physical table do not themselves prove source/physical simulation. The independent replay log is `/tmp/pa194-controller-halt-reach-replay.log`; check final PASS and process exit before relying on it.

The repository-source replay also passed using this directory for all three
source-directory arguments and the same retained overlays.
