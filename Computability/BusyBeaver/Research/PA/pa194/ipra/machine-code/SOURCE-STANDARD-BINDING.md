# Standard-natural binding to the repository source cycle

`PA194SourceStandardBinding.actualStepCycle` relates the actual finite PR controller step to the existing `M6.Source.cycleStep` over ℕ. At any standard source site i < 3673, for any standard encoded state with PC i and any nine-register vector represented by its nested-pair file, one PR step has the same encoded next control and represented register vector as the pinned source cycle. The accompanying `resolvedBinding` checks every instruction form, including normal source-root exit restarting at site 0, explicit halt, malformed resolution, and zero/positive decrement. The halt and malformed sentinels are 3674 and 3673 respectively.

The earlier `PA194SourceActualStepCalibration.actualStepCalibration` is an all-candidate-PRA-model theorem, but only for standard Lean natural source ordinals. This new theorem specializes to ordinary natural numbers to compare with the existing source implementation; it is not an all-model source-cycle theorem, model-length iteration, physical synchronization, scheduler calibration, or an object-iPRA/Con(PA) statement. It does not yet certify reachable PC bounds and total source resolution, nor identify the nested-pair file with the physical tape file.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-source-standard-binding.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged checker recompiles fifteen sources in a fresh common output, pins selected source and object hashes, rejects inherited Git overrides, and audits theorem axioms. The machine/source-tree baseline, graph/equality overlay, and project/package foundations remain prebuilt. Hash pins do not establish full transitive provenance or cross-overlay compatibility; this is not a self-contained source build.
