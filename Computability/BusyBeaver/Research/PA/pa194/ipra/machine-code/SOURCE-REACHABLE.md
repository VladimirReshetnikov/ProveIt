# Model-time reachability bound for the PR source controller

`PA194SourceSentinel` proves that the actual PR source step leaves a state unchanged when its encoded PC is malformed sentinel 3673 or halted sentinel 3674. Its `dispatchAvoid` theorem proves the finite selector falls through to its explicit default when the PC differs from every table ordinal.

`PA194SourceReachable.stepPCBound` combines the sentinel facts with the resolved-target bound and proves that every encoded state with model PC <3675 steps to another such state in every candidate PRA model. Valid source ordinals are 0..3672, normal source-root exit restarts at 0, failed instruction resolution maps to 3673, and the explicit halt maps to 3674. `runPCBound` uses the existing PR iterator recurrence, PR code graph definability and model IΣ₁ induction to prove the bound at every model-valued time, including nonstandard times, from any seed satisfying the bound.

This is a model-uniform Lean theorem for the newly defined PR controller run, not a native object-iPRA proof. The bound permits the malformed sentinel; exclusion requires a separately kernel-checked total-resolution theorem. Source/physical frame synchronization, correspondence to the abstract scheduler, and either direction of Con(PA) are not established. The finite table and machine-specific baseline are retained prebuilt as explained below.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-source-reachable.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged checker recompiles nineteen sources in one fresh output, pins selected source and object hashes, rejects inherited Git overrides, and audits theorem axioms. It retains the prebuilt machine/source-tree baseline, graph/equality overlay, and project/package foundations. The named hashes do not establish their full transitive provenance or cross-overlay compatibility; the replay is not a self-contained source build.
