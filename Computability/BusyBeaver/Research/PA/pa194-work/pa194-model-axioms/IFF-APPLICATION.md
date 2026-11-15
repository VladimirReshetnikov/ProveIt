# Contextual equivalence application

For arbitrary internal formulas p and q, contexts and proofs, these fixed parameter-free Σ₁ graphs compute the exact internal proof code for applying either direction of `(p → q) ∧ (q → p)`: the constructor consumes a proof of that formula and a proof of the relevant premise, both under the same context. Formula and proof codes may be nonstandard. These constructors directly support applications of the separation-trace equivalence in the minimum-bad argument.

The result is model-level for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ theories. Both input proofs remain hypotheses; this does not establish the complete minimum-bad contradiction, ordinal induction sequent, or native iPRA equivalence.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-context-iff.sh "$PWD" /dev/shm/pa194-context-iff-application-replay
```

The checker rebuilds the source against prebuilt dependency outputs, verifies direct hashes, checks six axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
