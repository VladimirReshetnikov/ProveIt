# Twelve positive variables: 111 operations, degree 1081

The preferred new artifacts are:

| Artifact | Positive unknowns | Equations | Exact degree | Binary operations |
|---|---:|---:|---:|---:|
| `positive12_product.json` | 12 | 1 | 1081 | 111 = 68M + 43A |
| `positive12_system.json` | 12 | 3 | 7, 2, 1072 | 107 = 66M + 41A |

The complete mathematical construction and proof are in `POSITIVE12_PROOF.md`.
Every auxiliary register is a computed expression, not an additional unknown.
The four exact coefficients are bound as one compact Wang943 tuple, with
compressed payloads included under `coefficients/`; the hashes refer to the
uncompressed unsigned little-endian integer bytes.

The synthesis improves the former local twelve-variable polynomial
(139 operations, degree 1257), package 20's wave-3 low-degree form
(123 operations, degree 1145), and package 21's wave-3 operation winner
(116 operations, degree 1353). It does not improve the variable count,
replace the 67-operation higher-variable equation, or claim an optimum.
Jones's explicit nine-variable specialization is a separate option.

The innovations are:

1. A single smaller weight M=k(I²+T²), L=HM+1 handles both inner-root
   separation and the main-root norm using the strict gap
   sqrt(G)-sqrt(A)>kY².
2. The main congruence carrier W=b0+Ht preserves direct positive completeness.
3. A quadratic remainder calculation in the trace and product of
   d(W±Lsqrt(G))² avoids the larger pair-ring norm expansion.
4. Sharing H²P and H²U between the two auxiliary coefficients saves a gate.

Run the locally authored scripts from any directory:

    python build_positive.py
    python check_positive.py

The checker uses the already available NumPy package; no software installation
is required. `CHECK_RESULTS.json` reports 180 independently evaluated
multiquadratic norms, 21 synthetic kernel witnesses, 500 strict-bound fixtures,
400 parity tests, two exact-degree specializations, all gate/port liveness,
and the four coefficient hashes. It also checks 12 assignments using residues
of the actual bound integers. These are diagnostic tests, not an accepting
K215 computation or a finite proof of Con(ZFC).

`SOURCE_PINS.json` records the upstream immutable pin, blob IDs and local hashes.
No received repository program was executed or imported, and no public repository
was changed. The new equivalence remains ordinary mathematics formalizable in
ZFC relative to the inherited compiler and literal machine-calibration proofs;
it is not a new proof-assistant theorem.
