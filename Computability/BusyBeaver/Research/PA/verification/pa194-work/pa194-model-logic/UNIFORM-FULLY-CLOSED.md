# Uniform graph for fully closed separation

`pureTermFreeBound`, `purePairFreeBound`, and `pureFormulaFreeBound` lift the existing free-index bound to every arithmetic IΣ₁ model. The fixed parameter-free Σ₁ formula `pureFormulaFreeBoundGraph` defines `pureFormulaFreeBound` uniformly; `pureFormulaFreeBound_model` identifies it definitionally with `formulaFreeBound` in each candidate PRA + IΣ₁ model.

`pureFullyClosedSepGraph` composes the existing uniform separation-root graph, the free-bound graph, and the uniform PR closure graph. `pureFullyClosedSepGraph_defined` proves that this one fixed Σ₁ formula defines `pureFullyClosedSeparation` in every arithmetic IΣ₁ model. `pureFullyClosedSeparation_model` identifies the result with the separately checked `fullyClosedSeparation` of the candidate model, including nonstandard inputs. The latter module supplies its scoped, shift-invariant output and target axiom-leaf properties under the stated validity/admission hypotheses.

A Σ₁ graph for a total constructor alone does not establish that its range is Δ₁. No bound is yet established here for an original separation-body witness in terms of its fully closed output. This module therefore does not construct a Δ₁ theory for parameterized separation, identify PA, connect to the physical machine, or prove a native iPRA result.

The incremental audit rebuilds all four modules and a five-report axiom audit in a fresh output against separately source-replayed uniform closure, fully-closed construction, compiler and classifier overlays. Remaining workspace dependencies are prebuilt. It is not a clean whole-workspace build. Reproduce from the repo with an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-uniform-fully-closed.sh "$PWD" NEW_EMPTY_OUTPUT \
  /dev/shm/pa194-uniform-closure-replay /dev/shm/pa194-fully-closed-replay \
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
