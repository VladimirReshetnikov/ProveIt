# Adjunctive and classifier-defined separation theory

`adjunctiveClosedSepTheory` is the union of the finite relational equality-plus-weak-adjunction theory `adjunctiveTheory` and `closedSepTheory`, the standard sentence theory defined by the uniform closed-separation classifier. `adjunctiveClosedSepTheoryDelta` constructs its actual Foundation `Theory.Δ₁` instance. In each candidate PRA model with an IΣ₁ arithmetic reduct, `adjunctiveClosedSepTheory_class` proves that the model-internal Δ₁ axiom class is exactly the union of the adjunctive axiom class and `closedSepCode`, including nonstandard codes.

`adjunctiveClosedSep_refutation_target` turns a coded internal refutation of this union into `TargetProvable 1`. Using the previously source-checked scheduler-fairness theorem, `adjunctiveClosedSep_provable_halts` concludes that some internal scheduler time k has `F haltAfter ![k] = 1`, and `adjunctiveClosedSep_consistent_of_nonhalting` is its contrapositive. No axiom supplier or admission bound is left as a hypothesis in these wrappers. The scheduler, proof and time codes are interpreted inside the given PRA + IΣ₁ model.

This theory has not been identified with PA or with the full, universally closed parameterized separation scheme. The result does not establish a correspondence with the physical 194-state machine and is not a native iPRA derivation or the requested Con(PA) equivalence. The uniform shift-fixed classifier defines the exact separation class handled here; no claim is made that it captures all needed parameterized instances.

The incremental source replay rebuilds the union module and its five-report audit top in a fresh output against the separately source-replayed closed-separation theory, uniform classifier, compiler and scheduler-fairness overlays. The scheduler-fairness output was built from 295 standalone source modules in retained phases; Foundation, BusyBeaver, FirstOrder and DiophantineConsistency workspace prefixes remain prebuilt. This is not a clean whole-workspace rebuild.

Reproduce from the repository using an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-adjunctive-closed-sep.sh "$PWD" NEW_EMPTY_OUTPUT \
  /dev/shm/pa194-closed-sep-theory-replay /dev/shm/pa194-uniform-sep-combined-replay \
  /dev/shm/pa194-standard-no-free-replay /dev/shm/pa194-closed-sep-classifier-replay \
  /dev/shm/pa194-fairness-full-source-replay /dev/shm/pa194-generic-sim-replay \
  /dev/shm/pa194-adjunctive-sim-v2-replay /dev/shm/pa194-shift-interface-replay \
  /dev/shm/pa194-unrestricted-existential-v2-replay /dev/shm/pa194-qf-ranked-existential-audit \
  /dev/shm/pa194-ranked-open-separation-replay-v2 /dev/shm/pa194-adjunctive-admission-audit \
  /dev/shm/pa194-general-shift-replay /dev/shm/pa194-general-reverse-shift-replay \
  /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-general-freshness-audit \
  /dev/shm/pa194-observational-general-audit /dev/shm/pa194-full-one-level-audit
```
