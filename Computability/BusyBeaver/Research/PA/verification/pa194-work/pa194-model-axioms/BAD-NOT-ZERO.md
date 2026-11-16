# A bad ordinal cannot be zero

For arbitrary valid internal arity-one property `p`, model-valued index `a`, and internal context Γ, `badNotZeroProof` consumes contextual derivations of the actual ordinal base statement, the ordinal-domain instance at `a`, and the negated property instance at `a`. It constructs a derivation of the negated zero instance at `a`. The fixed parameter-free Σ₁ graph is proved to compute the exact output derivation code, including for nonstandard formulas, indices, contexts and proof codes.

This is a model-level result for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ source theories. All three input derivations remain hypotheses. The complete minimum-bad contradiction, ordinal induction sequent, and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-bad-not-zero.sh "$PWD" /dev/shm/pa194-ordinal-bad-not-zero-replay
```

The checker rebuilds the source against prebuilt dependency outputs, verifies direct hashes, checks three axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
