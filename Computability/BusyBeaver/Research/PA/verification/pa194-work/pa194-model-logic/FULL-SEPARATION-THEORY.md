# Fully parameter-closed separation theory and modeled scheduler

`pureWitnessEnvelope` is the coded history obtained by iterated inverse opening, lifted to every arithmetic IΣ₁ model; `pureWitnessEnvelopeGraph` is its fixed parameter-free Σ₁ graph. In each candidate PRA + IΣ₁ model, it agrees with the separately source-checked `uncloseHistory q q`. The independently proved cancellation and history bounds imply `pureFullyClosed_property_bound`: for every internal arity-one body p, including nonstandard p, `p < pureWitnessEnvelope (pureFullyClosedSeparation p)`. This does not assume that binding preserves or increases formula codes.

`fullSepUniform` is a fixed parameter-free Δ₁ arithmetic formula. It requires the candidate code q to be shift-fixed and searches for an arity-one body p below the envelope whose fully closed separation code is q. The Σ₁ polarity existentially introduces the unique envelope value; the Π₁ polarity universally quantifies an envelope value and uses an implication from its Σ₁ graph. `fullSepUniform_defined` verifies both polarities in every arithmetic IΣ₁ model and `fullSepUniform_provablyProper` proves their equivalence over IΣ₁. `fullSepTheory` is defined as the standard source sentences recognized by this classifier, and `fullSepTheoryDelta` is its actual Foundation `Theory.Δ₁` instance; the explicit shift conjunct supplies the standard sentence witness.

In each candidate PRA + IΣ₁ model, `fullSepTheory_class` identifies the entire internal Δ₁ axiom class with all `fullyClosedSeparation p` for internal arity-one p, including parameterized and nonstandard bodies. Shift-fixity is automatic for those instances by the separately source-checked closure theorem, and the envelope bound makes the body search complete. `fullSepTheory_axiom_seed` supplies the corresponding target proof leaf at every admitted source axiom. The union `adjunctiveFullSepTheory` adjoins the finite equality-plus-weak-adjunction source theory; its model-internal axiom class is exactly that finite class or a fully closed instance. `adjunctiveFullSep_refutation_target` compiles an internal refutation to `TargetProvable 1`; `adjunctiveFullSep_provable_halts` yields some internal scheduler time k with `F haltAfter ![k] = 1`, and `adjunctiveFullSep_consistent_of_nonhalting` gives the contrapositive.

This is a theorem about the explicitly classifier-defined theory and the modeled scheduler. The standard typed Foundation separation schema has not yet been identified with this particular closure encoding, nor has the resulting theory been identified with PA. The result does not connect the modeled scheduler to the physical 194-state machine and is not a native iPRA derivation or the requested Con(PA) equivalence.

The incremental audit rebuilds all six modules and a 12-report axiom audit in one fresh output against separately source-replayed inverse-envelope, uniform-closure, fully-closed separation, compiler, and scheduler-fairness overlays. The scheduler fairness closure was itself built from 295 standalone source modules in retained phases. Foundation, BusyBeaver, FirstOrder, and DiophantineConsistency workspace dependencies remain prebuilt; this is not a clean whole-workspace build. Reproduce from the repo using an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-full-sep-theory.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-unclose-envelope-replay /dev/shm/pa194-uniform-fully-closed-replay \
 /dev/shm/pa194-uniform-closure-replay /dev/shm/pa194-fully-closed-replay \
 /dev/shm/pa194-model-separation-full-replay /dev/shm/pa194-model-separation-seeded-replay \
 /dev/shm/pa194-model-closure-definability-replay /dev/shm/pa194-model-closure-replay \
 /dev/shm/pa194-general-separation-replay /dev/shm/pa194-ranked-open-separation-replay-v3 \
 /dev/shm/pa194-closed-sep-theory-replay /dev/shm/pa194-uniform-sep-combined-replay \
 /dev/shm/pa194-standard-no-free-replay /dev/shm/pa194-closed-sep-classifier-replay \
 /dev/shm/pa194-fairness-full-source-replay /dev/shm/pa194-generic-sim-replay \
 /dev/shm/pa194-adjunctive-sim-v2-replay /dev/shm/pa194-shift-interface-replay \
 /dev/shm/pa194-unrestricted-existential-v2-replay /dev/shm/pa194-qf-ranked-existential-audit \
 /dev/shm/pa194-adjunctive-admission-audit /dev/shm/pa194-general-shift-replay \
 /dev/shm/pa194-general-reverse-shift-replay /dev/shm/pa194-unrestricted-all-replay \
 /dev/shm/pa194-general-freshness-audit /dev/shm/pa194-observational-general-audit \
 /dev/shm/pa194-full-one-level-audit
```
