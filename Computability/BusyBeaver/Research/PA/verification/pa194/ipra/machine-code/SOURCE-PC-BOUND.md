# Bounded PA194 source-controller program counters

`PA194SourceBoundedStep.boundedStepCalibration` lifts the previous standard-ordinal selector theorem to any model-valued PC below model numeral 3673: `PA194FiniteControls.modelBelowNumeral` yields a finite standard ordinal, and the resolved instruction semantics then apply. The existential finite ordinal is in the Lean metatheory; the theorem is not itself an object-language formula or an induction over model-valued ordinals.

`PA194SourceTargetBounds.literalInstructionBound` proves from the source resolver that any successfully resolved destination is a valid ordinal below 3673 or normal root exit. The proof is adapted from the retained PA196 upstream `InternalCodedSourceTable.lean` range lemmas, specialized to the exact PA194 source-program size. `PA194SourcePCBound.stepWorkingPCBound` combines the two results to prove, in every candidate PRA model, that any encoded source state with PC <3673 steps to PC <3675. Root exit goes to 0, unresolved resolution goes to malformed sentinel 3673, and the explicit halt instruction goes to halted sentinel 3674. This handoff does not exclude malformed resolution or by itself establish model-time reachability.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-source-pc-bound.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged checker recompiles seventeen sources together, pins selected source and object hashes, rejects inherited Git overrides, and audits theorem axioms. The machine/source-tree baseline, graph/equality-code overlay, and project/package foundations are retained prebuilt. These hashes do not establish full transitive provenance or cross-overlay compatibility; this is not a self-contained source build.
