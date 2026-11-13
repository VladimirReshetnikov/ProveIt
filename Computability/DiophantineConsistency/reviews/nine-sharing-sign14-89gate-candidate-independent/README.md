# Independent external 89-gate candidate review

PASS. Starting from the pinned 90-gate AST, the checker independently applies exactly one `q-(d+g) = (b-i)-g` rewrite with `q=b+1` and `d=i+1`, normalizes the identity in a free commutative ring, compares all five resulting residual ASTs and names, and confirms `b-i` was already used outside Nt. Exact ordered-subtree sharing gives 80 residual and 89 live operations including five squares and their sum: 35 additions, 16 subtractions and 38 multiplications.

This is an upper bound for this sharing convention, not a minimality proof. It is external Python evidence; Lean equivalence and JSON/PDF/fixed-port file correspondence remain separate.
