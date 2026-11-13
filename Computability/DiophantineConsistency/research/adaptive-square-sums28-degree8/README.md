# Candidate: 28 variables, degree eight, 132 circuit operations

This candidate deletes `varphiSquareVariable` from the 29-variable graph and substitutes the already-computed `mainScaleVariable * mainScaleVariable`. It removes the corresponding square constraint, square operation and sum operation. `generate.py` pins the parent and verifies topology and liveness. `verify_substitution.py` checks by exact integer-polynomial arithmetic that all 19 remaining parent residuals agree after substitution and that the removed residual becomes zero. `verify_degree.py` checks all 19 child residual degrees and verifies exact degree 8 with a port-independent leading monomial. The graph SHA-256 is `6ddad50448c27a371e27cd90f860e30ca8632c57d539f91c2f1c08f10ed1fd27`.

The witness maps delete the square coordinate or insert the positive
main-scale square. The AQ28→AQ27→AQ26 [author-only Lean extension](../../reviews/aq26-author-trial-v2/README.md)
compiled the model transports and native endpoints for this chain; its
[independent artifact audit](../../reviews/aq26-author-independent-audit/README.md)
passed. This is a historical hybrid, not a matched peer or current-source
result; the Foundation wrapper's outer exit and inherited package-transitive
and dynamic ancestry remain qualified. The finite degree check is not a Lean
degree theorem, and no minimum is claimed.
