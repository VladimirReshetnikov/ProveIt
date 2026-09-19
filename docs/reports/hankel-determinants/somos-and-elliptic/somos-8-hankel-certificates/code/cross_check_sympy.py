#!/usr/bin/env python3
"""Independent symbolic determinant audit. Optional dependency: SymPy.

The source recurrence is recomputed in SymPy's ZZ[r] polynomial domain;
all certificate moments and determinants are compared coefficient by coefficient.
"""
from __future__ import annotations
from pathlib import Path
import json
try:
    import sympy as s
    from sympy.polys.matrices import DomainMatrix
    from sympy.polys.domains import ZZ
except ImportError as exc:
    raise SystemExit("This optional audit needs SymPy: python -m pip install sympy") from exc

ROOT = Path(__file__).resolve().parents[1]
r = s.Symbol("r")
K = ZZ.poly_ring(r)
t = K.gens[0]
results = json.loads((ROOT/"data"/"certificates.json").read_text())
for result in results:
    k = result["family"]
    # Written independently from the certificate module.
    A = {11: [1, -t-1, -1, t],
         12: [1, -t-1, t-1, 0],
         13: [1, -t-1, t-2, t]}[k]
    a = [K.one]
    for n in range(1, 21):
        value = -t if n == 1 else K.zero
        value -= sum((A[j]*a[n-j] for j in range(1, min(n, 3)+1)), K.zero)
        if n >= 3:
            value += sum((a[i]*a[n-3-i] for i in range(n-2)), K.zero)
        if n >= 4:
            value -= t*sum((a[i]*a[n-4-i] for i in range(n-3)), K.zero)
        a.append(value)
    from_coeffs = lambda p: sum((v*t**i for i, v in enumerate(p)), K.zero)
    expected_a = [from_coeffs(p) for p in result["moments_0_to_20"]]
    if a != expected_a:
        raise AssertionError(f"Moment mismatch for C{k}")
    h = [K.one]
    for n in range(11):
        dm = DomainMatrix([[a[i+j] for j in range(n+1)] for i in range(n+1)],
                          (n+1, n+1), K)
        h.append(dm.det())
    if h != [from_coeffs(p) for p in result["hankels_minus1_to_10"]]:
        raise AssertionError(f"Determinant mismatch for C{k}")
    print(f"C{k}: all 21 moments and 12 determinants agree with SymPy {s.__version__}")
print("Independent symbolic audit PASS")
