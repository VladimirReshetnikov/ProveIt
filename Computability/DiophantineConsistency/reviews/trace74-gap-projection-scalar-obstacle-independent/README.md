# Review of the relaxed scalar family

The ordinary-integer family in the hash-pinned note satisfies the stated
strict Pell gap, zero projection, scalar rank residues and guard violation.
Its growth estimate is deliberately strong enough to imply
`c>2t*y_n≥k(Y+1)`, so the required second offset is negative. It is not a
positive graph tuple and does not refute the fixed-port guard.

Reviewed note SHA-256:
`6bb407ddbdc6f6aa3e9fc7bcb1a87688e62702dea7ca2bbf4f4d868757c89800`.
Checker SHA-256:
`b92fb3bd68e80bdc80cc4a6607162c83981c39a4c331893b60d434810c00a675`.
The checker was rerun with `python3 -I -S -B` and exited 0 for its exact
sample and symbolic exponent checks. It does not verify the universal
recurrence estimates, a full graph valuation, Lean proof or iPRA endpoint.
