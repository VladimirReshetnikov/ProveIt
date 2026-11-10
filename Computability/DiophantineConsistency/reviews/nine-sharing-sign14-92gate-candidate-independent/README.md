# Independent external 92-gate candidate review

PASS. The checker independently reconstructs the 93-gate input and applies the unique Nt reassociation `((x+b)-d)-z = (x+(b-d))-z`, verifies the free-ring identity, compares every resulting residual AST and row name to the pinned candidate, and confirms the difference `b-d` already occurs in another residual. Exact ordered-subtree sharing yields 83 residual operations and 92 live operations including five squares and their sum: 37 additions, 16 subtractions and 39 multiplications.

The count is an upper bound under this sharing convention, not a minimality proof. This is external Python evidence; Lean equivalence and external JSON/PDF/fixed-port file correspondence remain separate.
