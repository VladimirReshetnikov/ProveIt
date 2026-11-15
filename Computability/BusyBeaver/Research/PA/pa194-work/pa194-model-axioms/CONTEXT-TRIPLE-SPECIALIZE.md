# Contextual triple specialization

A fixed parameter-free Σ₁ arithmetic graph computes the exact internal proof code for specializing three nested universal quantifiers under an arbitrary shared context. The constructor consumes a proof of `∀∀∀ p` and yields a proof of `p[t,u,v]`, correctly composing the binder environments. It works for internally valid formula codes, terms, contexts and input proof codes including nonstandard values, in every covered candidate PRA model with IΣ₁ arithmetic reduct and every internal Δ₁ source theory.

The universally quantified proof remains a hypothesis; this constructor does not establish the least-point theorem, full minimum-bad contradiction, ordinal induction sequent or native iPRA equivalence.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-context-triple-specialize.sh "$PWD" /dev/shm/pa194-context-triple-specialize-repo
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks three axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
