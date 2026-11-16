# Total source resolution and model-time absence of malformed control

`PA194ResolveCheck` checks that a finite block of the actual pinned PA194 source tree resolves at every ordinal in the block. `generate-resolution.py` generates 15 Lean modules covering all 3,673 ordinals, each proved with `decide +kernel`, and an aggregator `PA194ResolvedComplete.allResolved`. No archived coverage-certificate object or mismatched coverage overlay is imported. Every generated block's printed axioms are `[propext]`; the aggregate reports `[propext, Quot.sound]`.

`PA194ResolvedModel.runValidPC` discharges the earlier `AllResolved` premise and proves: in every candidate PRA model whose arithmetic reduct satisfies IΣ₁, if the new PR source-controller run starts with PC either <3673 or equal to halted sentinel 3674, then at every model-valued time, including nonstandard times, the PC remains in that disjunction. Consequently the malformed sentinel 3673 is not reached. The proof includes source-root restart and absorbing halt.

This is a Lean model invariant, not a native iPRA theorem. It does not identify the source run with the literal physical run, establish physical frame synchronization or its cumulative clock, relate the source run to the abstract proof scheduler, or prove either Con(PA) implication. The source tree's pinned generator and table provenance are separately audited by the source-halt-site checker; this replay uses the retained unified baseline's source tree/program objects.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-resolved-controller.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged checker verifies named source and artifact hashes, rejects inherited Git overrides, recompiles twenty controller/iteration modules, regenerates and kernel-checks all fifteen resolution blocks, and compiles the aggregator and model invariant in the same fresh output, auditing printed axioms. It retains the prebuilt unified machine/source-tree baseline, graph/equality overlay and project/package foundations. The named hashes identify those retained objects but do not reconstruct or authenticate their entire transitive source closure or all cross-overlay compatibility. This is a staged replay, not a complete source rebuild.
