# Shifting the separation trace

For internally valid arity-one property `p` and model-valued index `s`, `shift_traceExists` proves the exact equation `shift (traceExistsCode p s) = traceExistsCode (shift p) (s + 1)`. The sources also give a fixed parameter-free Σ₁ graph for `traceExistsCode` and one for a contextual derivation transformer, proving that the latter graph outputs the exact internal derivation code. A proof of the original trace under context Γ yields a proof of the shifted trace under Γ.shift. All property codes, indices, contexts and input proofs may be nonstandard.

This is a model-level theorem for covered candidate PRA models with IΣ₁ arithmetic reducts and internal Δ₁ source theories; the input proof remains a hypothesis. It does not establish the full ordinal induction sequent or native iPRA equivalence.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-separation-trace-shift.sh "$PWD" /dev/shm/pa194-separation-trace-shift-replay
```

The checker rebuilds the source, checks hashes of its direct dependencies, checks six axiom reports, and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
