# A bad-trace member in the ordinal domain is nonzero

For every internally valid arity-one `p` and model-valued indices `s` and `x`, the constructor takes contextual proofs of: the opened separation trace for `¬p`; membership of `x` in its witness; the ordinal base statement for `shift p`; and the ordinal-domain instance at `x`. It derives a contextual proof that `x` is nonzero. Its fixed parameter-free Σ₁ graph computes exactly the output proof code, including for nonstandard property, index, context and proof codes. This composes the trace `hbad` and nonzero `hnz` local steps in the minimum-bad argument.

The result is model-level for covered candidate PRA models with IΣ₁ arithmetic reducts and internal Δ₁ source theories. All four input derivations remain hypotheses; the complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-trace-bad-not-zero.sh "$PWD" /dev/shm/pa194-trace-bad-not-zero-replay
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks three axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
