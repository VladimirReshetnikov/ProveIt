# Reverse membership consequence of a separation trace

For every internally valid arity-one property `p` and model-valued `s` and `x`, the constructor consumes contextual proofs of the opened separation trace, `x ∈ shifted-s`, and `shifted-p(x)`. It constructs a contextual proof of `x ∈ witness`, where the witness is free variable 0 and shifted-s is free variable `s + 1`. The fixed parameter-free Σ₁ graph computes exactly the output internal proof code; property, index, context and proof codes may be nonstandard. Together with the previous forward constructor, this supplies both directions of the actual trace membership equivalence.

The result is model-level for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ source theories. All three input derivations remain hypotheses. The full minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-trace-member-backward.sh "$PWD" /dev/shm/pa194-trace-member-backward-replay
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks three axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
