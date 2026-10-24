# Fixed binary-height direct consistency equation

Recommended natural equation: the sum of squares in residuals_affine.json, expanded by rebuilding as equation_affine.json, over16,036 nonnegative variables, exact degree4,700,865monomials.
Recommended unrestricted-integer equation: equation_integer.json, over27,916 integers, exact degree4,758,275monomials.

The flat-wire equation.json has32,223 natural variables and97k monomials; its smaller coefficients provide a different tradeoff. Read summary.json for the exact collected figures.

Source: one beta-coded obligation accumulator, proof labels bounded by an independent m, and M0=2^(2mN+1). The universal CRT coordinate bound U is not m. The fixed source theorem and arithmetic representation proofs are in the parent section.tex, with calibration independently audited in the sibling direct_audit packet.

All JSON coefficients are literal decimal integers. Each polynomial term [coefficient,[indices]] denotes the coefficient times the product of variables with those indices, repetitions allowed, zero-based indexing. No variable exponent or unevaluated arithmetic function occurs in these files.

Rebuild and check:
    python build_direct.py
    python check_direct.py
    python reduce_affine.py

check_direct.py uses explicit exceptions, so its tests also execute under python -O. Arithmetic source files are not executed.

The finite checks verify artifacts and bounded fixtures, not Con(ZFC). The equivalence proof is mathematical and is not claimed as a new end-to-end kernel certificate. No variable-count record or global optimality is claimed.

Compact storage: equation_integer.json is included in full. The affine map, nonnegativity residual list, and redundant expanded natural intermediates are reconstructed by build_direct.py and reduce_affine.py; verify_replay.py authenticates all twelve reconstructed outputs against frozen SHA-256 values.
