# Independent source review: natural-86 and shifted positive-74 bridge

The source-level ring cuts are valid over arbitrary commutative rings: the
shifted `q−F` cancels to `qm−n_F`, and the shifted guard cancels to
`g27−n_F−qm*n_h`. The checker proves both as exact sparse integer-polynomial
identities and replays the independent exact-DAG review plus the literal graph
source review. These establish the same four factor shapes, guard factor and
output at shifted coordinates in the stated source representation.

For the generic positive-shift source proof, the constant, variable, addition,
subtraction and multiplication cases match `Expr.subst` and `Expr.evalRing`;
the variable maps to its value plus one. Finite controls exercise those cases
over rings of characteristics 4, 12 and 17. The model statement applies the
existing `internalZero_iff` to each side and the ring equality at the same
natural-model valuation, with arbitrary signed ports and no positivity premise.

All source proofs and tactics remain unelaborated, including the potentially
large graph simplifications. This review is not a Lean, provider, iPRA,
symbolic-port-to-byte or PDF binding claim. No Lean was run.
