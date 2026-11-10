# Independent external 90-gate candidate review

PASS. Starting from the pinned 92-gate AST, the checker independently applies exactly four factorization replacements, compares all five resulting residual ASTs and names to the candidate, and normalizes the identity in the free commutative ring with `q=b+1` and `d=i+1`. The rank factor already occurs in the input. Exact ordered-subtree sharing yields 81 residual operations and 90 live operations including five squares and their sum: 36 additions, 16 subtractions and 38 multiplications.

The count is an upper bound for this sharing convention, not a minimum. This is external Python evidence; Lean equivalence and JSON/PDF/fixed-port file correspondence remain separate.
