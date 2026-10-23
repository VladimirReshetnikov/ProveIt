# Frozen compact Jones9 equation

The final candidate is `nu31/nine_compact_magnitude_tight.json`; the complete proof is `COMPACT_NINE_PROOF.md`. It has nine natural unknowns, degree `120724*5^32+366`, and 1,840 live binary arithmetic operations.

The 404 named constant leaves are fully bound: 402 coefficient polynomials, z, and y. The complete compact943 four-port tuple and z are materialized. The 402 derived coefficients and y are not materialized, but have bounded finite recipes in `nu31/COMPACT_CONSTANTS.json`. No fixed leaf is a free parameter. Historical source-default coefficient metadata is explicitly overridden by `nu31/COMPACT_COEFFICIENT_BINDING.json`.

## Reproduce with Python standard library

From a delivered package with sibling `arithmetic/`, `compiler/`, `review/`, and `nine/` directories:

    python nine/rebuild_nu31.py --compiler-root compiler
    python nine/verify_compact_instance.py nine/nu31 --compiler-root compiler

The first command independently rebuilds the parent coefficient records, proves the explicit index bound, regenerates every circuit node, and checks exact equality with the frozen circuit. The second reads the authentic four coefficient binaries, verifies hashes and bit lengths, evaluates the actual index modulo four primes, and compares 752 named circuit nodes with separately written formulas. It also checks 512 magnitude-companion assignments and 576 constructed finalizer witnesses.

Executable dependencies are only newly authored files from this review:

* `nine/rebuild_nu31.py`, `nine/prepare_coefficients.py`, `nine/build_compact_nine.py`, `nine/verify_compact_instance.py`;
* `review/generic_jones_circuit.py`, `review/optimize_nine_circuit.py`.

The independent degree audit additionally uses `review/audit_modified_nine.py` and its newly authored sparse-polynomial helper `review/independent_review_audit.py`; its final receipt is `review/NU31_INDEPENDENT_AUDIT.json`. No received upstream Python is executed. Lean files and received JSON are inert reviewed source/data, not evidence that a new kernel build ran.

`z_index.bin` is a minimal unsigned little-endian integer without header; its gzip form round-trips exactly. Its receipt is `Z_MATERIALIZATION.json`. The parent quartic is `arithmetic/quartic31.json`, and the underlying compiler proof/data are in `compiler/`.

The folders `check32/`, `rebuilt_nu31/`, and the older nu=32 comparison circuits are development artifacts and are not needed for a minimal delivery. Keep `nu31/`, the proof, the four new scripts listed above, the two circuit-construction dependencies, z materialization, the parent quartic, and the compact compiler tuple/proof.
