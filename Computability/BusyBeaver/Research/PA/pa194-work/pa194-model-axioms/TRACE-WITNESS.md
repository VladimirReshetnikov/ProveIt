# Existential witness from the specialized separation trace

For every internally valid property code `p` and model-valued index `s`, this proves that `traceExistsCode p s` is exactly an existential whose one-bound-variable body is `traceBodyCode p s`. The body is internally well scoped and has a fixed parameter-free Σ₁ graph. A second fixed Σ₁ graph computes exactly the code of an actual internal witness-elimination derivation: from a contextual proof of that existential and a branch proof using the opened, negated witness under the shifted conclusion and context, it constructs a proof of the conclusion. Property codes, indices, contexts and proof codes may be nonstandard.

This works model-by-model for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ source theories. Both input proofs remain hypotheses. An independent expanded trace-template identity, the full ordinal induction sequent, and native iPRA equivalence are not established.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-separation-trace-witness.sh "$PWD" /dev/shm/pa194-separation-trace-witness-replay
```

The checker rebuilds the source, verifies hashes of its direct dependencies, checks six axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
