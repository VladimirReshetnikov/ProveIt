# Forward membership consequence of a separation trace

For every internally valid arity-one property `p` and model-valued `s` and `x`, the constructor consumes contextual proofs of the opened separation trace and of `x ∈ witness`, where the witness is free variable 0. It constructs a contextual proof of `x ∈ shifted-s ∧ shifted-p(x)`, with shifted-s at free variable `s + 1`. The fixed parameter-free Σ₁ graph computes exactly the output internal proof code; property, index, context and proof codes may be nonstandard. The auxiliary free-variable membership-code function also has a fixed Σ₁ graph.

The result is model-level for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ source theories. Both input derivations remain hypotheses. The full minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-trace-member-forward.sh "$PWD" /dev/shm/pa194-trace-member-forward-replay
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks four axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
