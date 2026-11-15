# Uniform arithmetic classifier for separation roots

`sepRootGraph` is one explicit parameter-free Σ₁ arithmetic graph for `sepRootPure`, defined in every arithmetic model of IΣ₁ using Foundation's negation graph and Δ₀ constructor graphs. `closedSepUniform` is an explicit parameter-free Δ₁ arithmetic semisentence; `closedSepUniform_defined` proves it recognizes the bounded shift-fixed separation-root predicate in every arithmetic IΣ₁ model, and `closedSepUniform_provablyProper` proves its two polarities equivalent in IΣ₁.

The model-specific bridge `sepRootPure_model` identifies the pure constructor with the actual PA194 `sepRoot`; `closedSepUniform_model` then proves the same fixed arithmetic sentence recognizes the previously proved `closedSepCode` in every candidate model of PRA plus IΣ₁. Thus the existing seeded axiom-leaf result applies to every code satisfying the uniform classifier. The predicate's exact shift-fixed and bounded syntax definition is retained; it is not asserted to capture arbitrary parameterized separation.

This does not yet construct a `Theory.Δ₁` instance: standard arbitrary-natural-code decoding and the standard sentence/quotation membership correspondence remain to be proved. It also does not establish universally closed parameterized separation, identify PA, or prove machine/PA consistency equivalence. A separate checked lemma relates shift-fixed quoted standard typed semiformulas to semisentences; that alone does not decode arbitrary naturals. The numerical compiler remains model-uniform over PRA + IΣ₁, not a native iPRA derivation.

The incremental combined replay rebuilt `PA194ModelSepRootGraph`, `PA194ModelClosedSepUniform` and the QF-import audit top in a single output against separately source-replayed classifier, ranked separation, compiler and 328-module baselines. Five main axiom reports contain no `sorryAx`; workspace objects remain prebuilt. Run `check-uniform-sep-combined.sh` with the staged baselines as in the example below; the first baseline argument may be the existing `/dev/shm/pa194-uniform-sep-graph-replay`, but both source modules are rebuilt into the new output before the audit.

Example from the repository root with a fresh output:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-uniform-sep-combined.sh "$PWD" /dev/shm/pa194-uniform-sep-graph-replay /dev/shm/pa194-closed-sep-classifier-replay /dev/shm/pa194-generic-sim-replay /dev/shm/pa194-adjunctive-sim-v2-replay /dev/shm/pa194-shift-interface-replay /dev/shm/pa194-unrestricted-existential-v2-replay /dev/shm/pa194-qf-ranked-existential-audit /dev/shm/pa194-ranked-open-separation-replay-v2 /dev/shm/pa194-adjunctive-admission-audit /dev/shm/pa194-general-shift-replay /dev/shm/pa194-general-reverse-shift-replay /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-general-freshness-audit /dev/shm/pa194-observational-general-audit /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-uniform-sep-combined-repo
```
