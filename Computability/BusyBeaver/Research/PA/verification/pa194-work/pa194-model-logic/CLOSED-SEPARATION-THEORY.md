# Classifier-defined closed-separation theory

`sepRootPure_shift_fixed` proves in every ordered-ring model of IΣ₁ that if an internal code `p` satisfies `IsSemiformula SourceL 1 p` and `shift SourceL p = p`, then its coded separation root is shift-fixed. The statement covers nonstandard model elements and keeps the shift-invariance hypothesis explicit.

`closedSepTheory` is the set of standard source sentences whose quotations satisfy the previously constructed parameter-free arithmetic classifier `closedSepUniform`. `closedSepTheoryDelta` constructs an actual Foundation `Theory.Δ₁` instance for this particular theory. Its membership correspondence uses the constructor lemma and the existing theorem that a shift-fixed quote of a standard typed proposition comes from a semisentence; IΣ₁ properness is supplied by the previously proved uniform classifier. This is a classifier-defined standard theory, and the result does not identify it with an independently defined full separation scheme.

For every candidate PRA model whose arithmetic reduct satisfies IΣ₁, `closedSepTheory_class` identifies the model's internal Δ₁ axiom class, including nonstandard codes, exactly with the bounded `closedSepCode` predicate. `closedSepTheory_refutation_target` then proves that a coded internal refutation of this theory yields `TargetProvable 1`, using the previously checked seeded axiom supplier and generic refutation compiler. Its premise is an internal refutation of this explicitly constructed theory; it is not a PA-refutation theorem. It does not include all universally closed parameterized separation, identify PA, connect the target proof to physical-machine execution, or prove a native iPRA result.

The incremental audit rebuilds all three modules and a four-report axiom audit in one independent output, against the prior uniform-classifier, standard-no-free and compiler replay overlays; all other workspace dependencies remain prebuilt. It is not a clean whole-workspace build. Reproduce from the repository using an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-closed-sep-theory.sh "$PWD" NEW_EMPTY_OUTPUT \
  /dev/shm/pa194-uniform-sep-combined-replay /dev/shm/pa194-standard-no-free-replay \
  /dev/shm/pa194-closed-sep-classifier-replay /dev/shm/pa194-generic-sim-replay \
  /dev/shm/pa194-adjunctive-sim-v2-replay /dev/shm/pa194-shift-interface-replay \
  /dev/shm/pa194-unrestricted-existential-v2-replay /dev/shm/pa194-qf-ranked-existential-audit \
  /dev/shm/pa194-ranked-open-separation-replay-v2 /dev/shm/pa194-adjunctive-admission-audit \
  /dev/shm/pa194-general-shift-replay /dev/shm/pa194-general-reverse-shift-replay \
  /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-general-freshness-audit \
  /dev/shm/pa194-observational-general-audit /dev/shm/pa194-full-one-level-audit
```
