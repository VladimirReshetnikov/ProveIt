# Uniform universally closed ordinal-induction statement

The single parameter-free Σ₁ arithmetic formula `closedOrdinalInductionGraph` defines `closedOrdinalInductionCode` across the covered models (PRA with IΣ₁ for the induced arithmetic). For every internal arity-one source property, including nonstandard codes, the resulting source formula has arity zero and is fixed by free-variable shift. For each standard typed property, it is exactly the quotation of `(inductionStatement p).univCl`.

The three checked theorems are `closedOrdinalInductionGraph_defined`, `closedOrdinalInduction_sentence`, and `closedOrdinalInduction_quote`. The graph composes the previously replayed ordinal statement constructor with the uniform free-variable-bound and model-close graphs. These are syntax and definability results. They do not provide an internal proof of the induction statement, a PA-to-source proof translator, or an iPRA consistency equivalence.

To replay this add-on against the specified prebuilt prerequisites into a fresh output, run

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-ordinal-closed.sh "$REPO" FRESH_OUTPUT
```

The passing output is `/dev/shm/pa194-ordinal-closed-replay` and its log is `/tmp/pa194-ordinal-closed-replay.log`. The checker checks the source and immediate prerequisite hashes, compiles the source, and checks its three axiom reports for `sorryAx`. Transitive prerequisites are prebuilt and are not source-replayed by this add-on.
