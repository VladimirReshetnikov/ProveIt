# Sign24 Lean degree upper bound draft

This source-only draft adapts the existing structural degree bound in
`QuadraticRegisterSystem.lean` to the sign24 expression. The first theorem
proposes a generic Lean proof that `Expr.toPolynomial.totalDegree` is bounded
by syntax degree. The second module proposes checking that the **actual Lean**
`Sign24AbstractExpression.expression p` has syntax degree exactly eight for
every integer port vector `p`, and hence its polynomial degree is at most eight.
It specializes the bound to `Sign24CurrentExpression.expression` as well.

This approach does not require normalizing the large port constants, because
each is treated as a coefficient. The proposed reflexive syntax computation
and polynomial proofs are uncompiled and could fail or exceed resources.
Even if checked, the result is only an upper bound, not a proof of exact degree
eight, JSON/port-byte equivalence, a numerical export or a Jones applicability
theorem. A guarded current-expression producer survey, prelaunch review and
exclusive Lean slot are required before testing.
