# Expanded opened separation trace

For every internally valid arity-one `p` and model-valued indices `s` and `x`, `traceAt_expanded` proves the exact typed formula equality between the specialization of the previously constructed opened separation trace and

```
(x ∉ witness ∨ (x ∈ shifted-s ∧ shifted-p(x))) ∧
((x ∉ shifted-s ∨ ¬shifted-p(x)) ∨ x ∈ witness).
```

The witness is free variable 0, the shifted source set is free variable `s + 1`, and `shifted-p(x)` is the shifted property instantiated at free variable `x`. The proof uses typed substitution composition and applies to nonstandard model-valued property codes and indices.

`expandedTraceAtProof` consumes an actual contextual proof of the opened trace and returns an internal derivation of this expanded formula. Its output code is exactly the already-checked fixed Σ₁ trace-specialization graph. This is a model-level result for covered candidate PRA models with IΣ₁ arithmetic reducts and internal Δ₁ source theories. The input trace proof remains a hypothesis; the complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-expanded-trace.sh "$PWD" /dev/shm/pa194-expanded-trace-at-replay
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks seven axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
