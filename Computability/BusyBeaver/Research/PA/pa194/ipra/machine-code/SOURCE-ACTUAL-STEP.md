# PA194 source-controller step with register-vector calibration

`PA194SourceRegisterRelation` defines what it means for the nested-pair model file to encode a vector of nine model-valued source registers. It constructs such a file for every vector and arbitrary residual tail, and proves that updating one register changes the represented vector exactly by `Function.update`.

`PA194SourceInstructionCalibration.instructionCalibration` proves that all instruction forms, including both decrement branches, cyclic normal exit, explicit halt and malformed resolution, act on the encoded PC and register vector as the defined model-valued instruction executor specifies. Increment/decrement use the interpreted candidate-PRA successor and predecessor codes. `PA194SourceActualStepCalibration.actualStepCalibration` composes this with the finite selector bound directly to the pinned source tree: for each **standard Lean natural** i < 3673 and each model-valued state whose encoded PC equals numeral i, the actual PR source-step code selects the resolved instruction and produces its specified PC and represented register vector.

This is not yet a proof of agreement with the existing `M6.Source.cycleStep` object or of model-length iteration: the executor must still be related to the source semantics and the source's arithmetic, with reachable PC/table-totality and the source physical frame/clock representation established. Nor does this show scheduler correspondence, a model-uniform physical/scheduler simulation, or a native-iPRA/Con(PA) implication. In particular, a standard finite-index theorem is not a blanket statement over nonstandard model PCs.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-source-actual-step.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker pins selected source and object hashes, rejects inherited Git overrides, and recompiles fourteen sources in a fresh common output with axiom audits. The source tree/program and machine baseline, graph/equality-code overlay, and project and package foundations remain prebuilt; hashes do not establish their full transitive provenance or all cross-overlay compatibility. This is a staged replay, not a self-contained build.
