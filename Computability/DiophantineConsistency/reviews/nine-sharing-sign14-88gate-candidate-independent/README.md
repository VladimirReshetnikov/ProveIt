# Independent external 88-gate candidate review

PASS. Starting from the pinned 89-gate AST, the checker independently applies the unique Nt rewrite `b-(i+1)=(b-i)-1`, normalizes the free-ring identity, compares all five resulting residual ASTs and row names, and confirms that `b-i` already appears outside Nt. Exact ordered-subtree sharing gives 79 residual and 88 live operations including five squares and their sum: 34 additions, 16 subtractions and 38 multiplications.

The count is an upper bound under this sharing convention, not a minimality proof. This is external Python evidence; Lean equivalence and JSON/PDF/fixed-port file correspondence remain separate.
