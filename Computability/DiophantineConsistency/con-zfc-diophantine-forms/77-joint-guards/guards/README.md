# Residue orientation with a native positivity guard

Primary results: 37 unrestricted integers at degree4,31 at degree6,26 at
degree8. Each polynomial is a fully fixed sum of squared explicit JSON
residuals. These compose source70's residue orientation with source71's
calibrated determinant guard. Both use the same complete source34 tuple.
Read PROOF.md for the arbitrary-signed soundness argument, simultaneous
canonical completeness, and inherited formalization boundary.

Use determinant37_quartic_direct.json for the primary quartic;
determinant37_quartic_affine.json supports the polynomial projections
in determinant31_sextic.json and determinant26_octic.json. Weighted-cone
alternatives have identical dimensions but a larger coefficient payload.
No smallest-possible polynomial or new kernel proof is claimed.

Run from any directory with Python3 and SymPy:

    python build_coefficients.py
    python build.py
    python check.py

The same commands run with -O. Coefficient paths are relative to each
polynomial JSON's directory. COEFFICIENT_BINDING.json supplies actual raw
integer digests and explicit new-scale recipes. Upstream sources, original
notices/licenses and mathematical dependencies are preserved and sealed in
UPSTREAM_COPY_RECEIPT.json. Source70/69/71 were obtained from the authenticated
arrival at9513bd88cefb762dc07e1872be3078d14aca63fe, reviewed at repository
pin2605669a532342f153b13eb6b4a0af4b54f5fa37.

METRICS.json counts expanded monomials after collecting polynomial
coefficients in fixed ports. Do not compare that number to upstream counts
that treat the ports themselves as separate monomial coordinates.
