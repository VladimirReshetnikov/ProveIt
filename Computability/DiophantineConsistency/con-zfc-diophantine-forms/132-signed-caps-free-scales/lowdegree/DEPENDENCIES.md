# Dependency and licensing boundary

This result's immediate arithmetic sources are pinned and copied in `source/`:

1. Round-15 degree-48 first-root carrier and literal equation.
2. The earlier first-root CRT carrier's complete ordinary proof.
3. Centered-budget soundness, half-binomial extraction and canonical completeness with a uniform margin.
4. Signed quadratic main projection, including main-root recovery and the signed ratio/whole-product prefix.
5. The normalized strong-rank and auxiliary step-down source interface.

The six coefficient payloads are copied byte for byte from the round-15 carrier. `coefficients/BINDING.json` gives their literal integer interpretation; `review/audit.py` checks each against a hardcoded authenticated SHA-256 digest, the bit lengths, the exact beta and cone powers, and mask inequalities. MF is already shifted.

The full inherited native/compiler/refutation chain and upstream licenses remain in the archive's retained round-15 closure. Copied immediate proofs do not by themselves substitute for that full source closure. This branch adds a new ordinary arithmetic reduction only; it does not claim a new calibration, consistency proof, global minimum, or end-to-end formal-kernel certificate.

`circuit.py` derives unchanged from the prior open-source evaluator. The new budget schedule and the elementary Klo factorization are pointwise polynomial identities. No coefficient or machine has been changed.
