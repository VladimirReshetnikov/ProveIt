# Explicit substitution beneath internal quantifier blocks

`PA194QVecBasis.qvec_basis` identifies the iteration of Foundation's `qVec` on `[&0]` for an arbitrary model length `k`: it is a well-formed substitution vector at depth `k` with entries `#0, …, #(k−1), &0`. The theorem applies to nonstandard `k` and uses an internal iteration history.

`PA194FreeBlockBasis.free_block_basis` combines that identification with substitution distribution: opening one quantifier outside a `k`-long universal block preserves that block and substitutes this precise vector into the shifted body. Both statements hold in every IΣ₁ arithmetic model, with arbitrary internally well-formed formula codes.

This identifies a single opening beneath a model-length quantifier block. It does not yet compose those vectors across the full opening history, identify the final code with `subst (fvarVec n) p`, construct induction-axiom closure bodies, prove comprehension, or establish an iPRA implication.

The author replay ran `check-free-block-basis.sh` against the pinned Foundation overlay, rebuilding seven local modules. Printed axioms are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
