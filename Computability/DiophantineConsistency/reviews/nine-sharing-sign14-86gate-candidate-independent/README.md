# Independent external 86-gate candidate review

PASS. Starting from the pinned 87-gate AST, the checker independently applies four `(a+r)-R = a-(R-r)` rewrites to two distinct shared residual subexpressions, normalizes the free-ring identity, and compares all five resulting residual ASTs and row names. Exact ordered-subtree sharing yields 77 residual and 86 live operations including five squares and their sum: 30 additions, 18 subtractions and 38 multiplications.

This is an upper bound under the stated sharing convention, not a minimality proof. Lean equivalence and external JSON/PDF/fixed-port file correspondence remain separate. The author records the first failed count-of-two attempt and corrected four-occurrence run.
