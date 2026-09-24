#!/usr/bin/env python3
"""Optional symbolic audit of the first-shift factorization; requires SymPy."""
import json
from pathlib import Path
import sympy as sp


def main():
    r = sp.symbols("r")
    # Normalize b_2 to 1. The other normalized two-block coefficients follow
    # from b_n = 2*b_(n-1) + binomial(n+2*r-3, r-1).
    u = 2*r/(r+1)
    v = 2*r*(2*r+1)/((r+1)*(r+2))
    w = 2*r*(2*r+1)*(2*r+2)/((r+1)*(r+2)*(r+3))
    A = sp.Integer(1)
    B = 2 + u
    D = 4 + 2*u + v
    G = 8 + 4*u + 2*v + w
    delta2 = [B-2*A, D-2*B+A, G-2*D+B]
    computed = sp.factor(delta2[0]*delta2[2]-delta2[1]**2)
    expected = -(r-2)*(r-1)*(r*r+11*r+6)/((r+1)*(r+2)**2*(r+3))
    if sp.cancel(computed - expected) != 0:
        raise AssertionError("Rational identity failed")
    report = {"status": "symbolic rational identity verified",
              "normalized_coefficient": str(computed),
              "sympy_version": sp.__version__,
              "scope": "formal rational identity, not a proof-assistant check"}
    out = Path(__file__).resolve().parents[1] / "data" / "symbolic_identity.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
