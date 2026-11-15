# Uniform arithmetic graph for iterated binding

`pureBindTerm` and `pureBindPair` lift the existing source variable-binding operations to every arithmetic IΣ₁ model. Their fixed arithmetic graphs are respectively `bindTermGraph` and `bindPairGraph`. `pureFormulaCloseConstruction` interprets the existing `FormulaClose.blueprint` in that generality, and `pureCloseIterConstruction` interprets the existing fixed PR closure-iteration blueprint. `pureModelClose_defined` proves the fixed Σ₁ graph `closeIterBlueprint.resultDef` defines `pureModelClose` in every arithmetic IΣ₁ model. `pureModelClose_model` identifies it definitionally with the existing `modelClose` for each candidate PRA model with IΣ₁ arithmetic reduct. The model elements can be nonstandard.

This is uniform definability of the iterated closure constructor. It does not construct a Δ₁ classifier for parameter-closed separation: in particular no bound on an original separation-body code in terms of its fully closed code is established here. It does not identify PA, prove a machine-halting equivalence, or yield a native iPRA derivation.

The incremental source replay rebuilds both modules and a four-report axiom audit in one fresh output against the separately source-replayed closure, compiler and classifier overlays. Remaining workspace dependencies are prebuilt. It is not a clean whole-workspace build. Reproduce from the repo using an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-uniform-close.sh "$PWD" NEW_EMPTY_OUTPUT \
  /dev/shm/pa194-model-separation-full-replay /dev/shm/pa194-model-separation-seeded-replay \
  /dev/shm/pa194-model-closure-definability-replay /dev/shm/pa194-model-closure-replay \
  /dev/shm/pa194-general-separation-replay /dev/shm/pa194-ranked-open-separation-replay-v3 \
  /dev/shm/pa194-closed-sep-theory-replay /dev/shm/pa194-uniform-sep-combined-replay \
  /dev/shm/pa194-standard-no-free-replay /dev/shm/pa194-closed-sep-classifier-replay \
  /dev/shm/pa194-generic-sim-replay /dev/shm/pa194-adjunctive-sim-v2-replay \
  /dev/shm/pa194-shift-interface-replay /dev/shm/pa194-unrestricted-existential-v2-replay \
  /dev/shm/pa194-qf-ranked-existential-audit /dev/shm/pa194-adjunctive-admission-audit \
  /dev/shm/pa194-general-shift-replay /dev/shm/pa194-general-reverse-shift-replay \
  /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-general-freshness-audit \
  /dev/shm/pa194-observational-general-audit /dev/shm/pa194-full-one-level-audit
```
