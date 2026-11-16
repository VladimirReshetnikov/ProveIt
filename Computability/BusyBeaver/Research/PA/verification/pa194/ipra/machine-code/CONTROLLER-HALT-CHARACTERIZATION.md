# Actual encoded-controller halt and source site 10

`PA194SourceHaltUnique.resolvedHaltIndex` proves that any actual source-program ordinal resolving to `.halt` is 10, by combining the kernel-checked unique halt leaf with an ordinal uniqueness lemma. `PA194ControllerHaltCharacterization.nextHaltIffSite10` proves in every PRA model that, when the actual encoded controller's current PC is below 3,673, its next PC is the halted sentinel 3,674 exactly when the current PC is site 10. The theorem does not assume all source instructions resolve.

`PA194ControllerHaltRun.nextHaltValid` extends the one-step characterization to a current PC that is either working or already halted. `runSuccessorHalt` applies this at any model time of the actual encoded controller iteration, with an explicit valid-current-PC premise and the additional IΣ₁ model assumption used by the iteration-successor theorem. These are semantic Lean model theorems, not native iPRA derivations. They identify the encoded source controller's own hit condition; they do not identify a scheduler hit, establish model-uniform physical/source synchronization, or prove either consistency implication.

The three new sources, in order, are `PA194SourceHaltUnique.lean`, `PA194ControllerHaltCharacterization.lean`, and `PA194ControllerHaltRun.lean`. Invoke the fresh-output checker from the repository root with:

```
/dev/shm/pa194-source-haltbridge/check-controller-halt-characterization.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-source-haltbridge
```

`/tmp/pa194-controller-halt-characterization-replay.log` records exit 0 and PASS. The checker regenerates the pinned source tree, rebuilds the tree/program and unique-halt-leaf theorem together with the encoded-controller source suffix and the three new sources, checks a pinned literal table hash, and audits the relevant axiom reports for `sorryAx`. The source tree, generated source hash, and literal table provenance do not by themselves establish their required source-to-physical simulation. The unified machine baseline, graph overlay, and foundations remain prebuilt; selected hashes do not authenticate their entire transitive closure.

The repository-source replay also passed using this directory for all three
source-directory arguments, with the same retained overlays.
