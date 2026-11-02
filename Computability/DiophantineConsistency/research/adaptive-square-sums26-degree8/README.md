# Candidate: 26 variables, degree eight, 126 circuit operations

This candidate deletes `scaledIndexVariable` from the 27-variable graph and substitutes the existing `cSquareVariable * i`. It removes the corresponding residual, square operation and sum operation. `generate.py` pins the parent and verifies topology and liveness. `verify_substitution.py` checks by exact integer-polynomial arithmetic that all 17 remaining parent residuals agree after substitution and that the removed residual becomes zero. `verify_degree.py` checks all 17 child residual degrees and verifies exact degree 8 with a port-independent leading monomial. The graph SHA-256 is `d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5`.

The witness maps delete the scaled-index coordinate or insert the positive
product `cSquareVariable * i`. The AQ28→AQ27→AQ26 [author-only Lean extension](../../reviews/aq26-author-trial-v2/README.md)
compiled the model transports and native endpoints; its [independent artifact
audit](../../reviews/aq26-author-independent-audit/README.md) passed. This is a
historical hybrid, not a matched peer or current-source result; the Foundation
wrapper's outer exit and inherited package-transitive and dynamic ancestry
remain qualified. A standard-theory client is being checked separately. The
finite degree check is not a Lean degree theorem, and no minimum is claimed.
