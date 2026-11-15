# Contextual projections and contradiction

The sources define fixed parameter-free Σ₁ arithmetic graphs, actual internal derivation constructors, and exact output-code equations for each projection of a conjunction and for contextual contradiction. For each covered candidate PRA model with IΣ₁ arithmetic reduct, these work for arbitrary internal Δ₁ source theories, contexts, valid formulas, and proof codes, including nonstandard values. The projection constructors consume a proof of the conjunction; the contradiction constructor consumes proofs of a formula and its negation and yields a proof of any chosen conclusion, all under the same context.

These are proof-rule constructors with explicit input-proof hypotheses. They do not establish the ordinal induction sequent or a native iPRA theorem.

From the repo root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-context-projections.sh "$PWD" /dev/shm/pa194-context-projections-contradiction-replay
```

The checker rebuilds both sources in one output and verifies source and direct dependency hashes. Its nine axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; it rejects `sorryAx`.
