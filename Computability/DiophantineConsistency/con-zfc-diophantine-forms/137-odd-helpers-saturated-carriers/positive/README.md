# New ten-positive operation frontier

- `equation_81.json`:81 live binary operations, exact degree750.
- `equation_82.json`:82 live binary operations, exact degree560.

These combine canonical Y=q^3s normalization with the incoming doubled-Pell product-square construction. They save three gates over the latest inspected84/436 and85/328 source133 points, with a degree tradeoff. Both preserve the complete directly indexed BFS943 coefficient tuple and the original positive-zero/refutation calibration. They do not reduce the number of variables or claim a global minimum or a new formal endpoint.

Full unbounded root/sign/decoding/completeness and degree proofs are in PROOF.md. Reproduce with:

    python -B build.py --check
    python -B verify.py
    python -B -O build.py --check
    python -B -O verify.py
