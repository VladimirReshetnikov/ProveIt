# Candidate: 27 variables, degree eight, 129 circuit operations

The [base-10 candidate display](../../equation8-27.pdf) includes the complete
129-operation circuit. Its [independent presentation audit](../../reviews/equation8-27-independent-audit/README.md)
checks the printed gates, aliases, residuals and reproducible PDF; it does not
establish the pending Lean transports.

This candidate deletes `ellProductVariable` from the 28-variable graph and substitutes the already-computed `ellVariable * (ellVariable + eta + zeta)`. It removes the corresponding residual, square operation and sum operation. `generate.py` pins the parent and verifies topology and liveness. `verify_substitution.py` checks by exact integer-polynomial arithmetic that all 18 remaining parent residuals agree after substitution and that the removed residual becomes zero. `verify_degree.py` checks all 18 child residual degrees and verifies exact degree 8 with a port-independent leading monomial. The graph SHA-256 is `1982b2f164b9b72f965050e3a26cec751f7d0839c2da0cbe3cc020b7e6fc0170`.

The proposed witness maps delete the product coordinate in a positive parent zero, and insert `ellVariable * (ellVariable + eta + zeta)` in a positive child zero. The inserted product is positive because its factors are positive. Over an ordered integral domain, the sum-of-squares zero condition forces every residual to vanish, so the exact identities support both maps. The corresponding Lean model theorem and native iPRA bridge remain open. The finite scripts establish neither nonstandard-model transport nor iPRA provability, and the size is not a minimality claim.
