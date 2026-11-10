# Source-only 90-gate Lean transfer draft

The draft replaces the shared 92-gate R term by `shared14' * shared08 + shared09`,
reusing the previously factored rank term. It proposes generic ring evaluation
equality of both changed residuals and the full seed. It is not elaborated or
checked; it needs an independent source-to-AST comparison, guarded Lean runs,
polynomial/model/degree transfers and iPRA endpoint. External file and fixed
port bindings remain separate.

The [independent structural review](../../reviews/nine-sharing-sign14-90gate-lean-draft-independent/README.md)
matches all five expanded draft residuals to the 90-gate candidate. This is
not a Lean compilation or proof of correspondence to external files.
