#!/usr/bin/env python3
"""Optional symbolic verification of the rational identities in the proof.

Requires SymPy. The main verifier and the proof do not depend on this script.
"""
import json
from pathlib import Path
import sympy as sp

n, r, t, m, T = sp.symbols("n r t m T")
h = lambda z: (n + 1 - z) * (n - 1 - 2 * z) / ((z + 1) * (n + 1 - 2 * z))
y = n + 1 - r - t
left = h(t) * h(y - 1) - 1
right = -r * (n + 1) * (n + 2 - r**2 + (n - r - 2*t)**2) / (
    (t + 1) * y * (n + 1 - 2*t) * (n + 3 - 2*y)
)
checks = {}
checks["ratio_identity"] = sp.cancel(left - right) == 0
central_left = 2 - m / (m - r + 1) - (m - r) / (m + 1)
central_right = (2*m - r + 2 - r**2) / ((m + 1) * (m - r + 1))
checks["central_difference_identity"] = sp.cancel(central_left - central_right) == 0
boundary = (n + 2 - r**2 + (n - r - 2*t)**2).subs(n, r**2 - 3)
T_value = (r**2 - r - 2) / 2
checks["boundary_factorization"] = sp.expand(boundary - 4*(T_value-t)*(T_value-t-1)) == 0
if not all(checks.values()):
    raise RuntimeError(str(checks))
report = {"status": "PASS", "sympy": sp.__version__, "checks": checks}
path = Path(__file__).resolve().parents[1] / "data" / "symbolic_report.json"
path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
