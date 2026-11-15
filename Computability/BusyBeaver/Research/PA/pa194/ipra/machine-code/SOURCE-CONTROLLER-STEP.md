# Model semantics for the encoded source-controller instruction

`PA194SourceInstructionModel.instructionModel` proves the model semantics of the actual finite PR instruction compiler for every resolved source instruction: increment, zero/positive decrement, jump including cyclic root exit, explicit halt, and failed resolution. Its nested-pair register interpretation is supplied by the separately checked register read/write laws.

`PA194SourceControllerStep.actualInstructionStep` composes that instruction theorem with `selectActual`, relating the generated PR step code to the instruction resolved directly from the pinned PA194 source tree at any **standard Lean natural** ordinal i < 3673, for arbitrary model-valued registers. The concrete all-model theorems `site10Step`, `site25Zero`, and `site25Positive` give respectively the halted sentinel and the exact register-8 conditional transitions 27/26. The code's iteration is defined with the checked generic PR iterator.

This is not yet a theorem that the encoded run agrees with `M6.Source.cycleStep` for an actual source-state encoding at every model time. In particular, a definition and proof for file/register representation relative to the source's model and physical tape are still needed, as are reachable PC/table totality, initialization, source/scheduler calibration, and physical synchronization. Standard ordinal quantification is not a model-quantified induction over arbitrary nonstandard PCs or times. The result is a Lean model theorem, not an iPRA consistency implication.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-source-controller-step.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The wrapper checks pinned inputs and named objects, rejects inherited Git overrides, and recompiles eleven modules together in a fresh output with axiom audits. The machine baseline including source tree/program, code-graph/equality overlay, and project/package foundations remain prebuilt. The named hashes and baseline manifest do not establish their full transitive provenance or cross-overlay compatibility; this is a staged replay, not a self-contained full build.
