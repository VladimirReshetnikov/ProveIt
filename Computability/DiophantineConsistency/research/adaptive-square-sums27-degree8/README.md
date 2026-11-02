# Candidate: 27 variables, degree eight, 129 circuit operations

The [base-10 candidate display](../../equation8-27.pdf) includes the complete
129-operation circuit. The original [presentation audit](../../reviews/equation8-27-independent-audit/README.md)
checks the printed gates, aliases and residuals; the [status-refresh audit](../../reviews/equation8-27-author-status-audit/README.md)
checks the revised disclosure and reproduced PDF. These display checks do not
themselves verify the Lean transports.

This candidate deletes `ellProductVariable` from the 28-variable graph and substitutes the already-computed `ellVariable * (ellVariable + eta + zeta)`. It removes the corresponding residual, square operation and sum operation. `generate.py` pins the parent and verifies topology and liveness. `verify_substitution.py` checks by exact integer-polynomial arithmetic that all 18 remaining parent residuals agree after substitution and that the removed residual becomes zero. `verify_degree.py` checks all 18 child residual degrees and verifies exact degree 8 with a port-independent leading monomial. The graph SHA-256 is `1982b2f164b9b72f965050e3a26cec751f7d0839c2da0cbe3cc020b7e6fc0170`.

The witness maps delete the product coordinate or insert the positive product
`ellVariable * (ellVariable + eta + zeta)`. The AQ28→AQ27→AQ26 [author-only
Lean extension](../../reviews/aq26-author-trial-v2/README.md) compiled the model
transports and native endpoints; its [independent artifact audit](../../reviews/aq26-author-independent-audit/README.md)
passed. This is a historical hybrid, not a matched peer or current-source
result; the Foundation wrapper's outer exit and inherited package-transitive
and dynamic ancestry remain qualified. The finite degree check is not a Lean
degree theorem, and no minimum is claimed.
