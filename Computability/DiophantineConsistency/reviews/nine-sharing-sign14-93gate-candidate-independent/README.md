# Independent external 93-gate candidate review

PASS. The checker independently reconstructs the 94-gate input, replaces exactly four occurrences of `b*(b+1)+g-b*(i+1)` with `b*(b-i)+g`, and compares all resulting ordered residual ASTs and row names with the pinned candidate. Sparse polynomial normalization checks the identity in a free commutative ring. Exact ordered-subtree sharing finds 84 residual operations and 93 live operations including five squares and their sum: 37 additions, 17 subtractions and 39 multiplications.

The count is an upper bound for this sharing convention, not a minimality proof. This is external Python evidence; Lean equivalence and JSON/PDF/fixed-port file correspondence remain separate.
