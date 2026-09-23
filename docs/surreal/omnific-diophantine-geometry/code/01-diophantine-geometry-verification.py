#!/usr/bin/env python3
"""Finite checks supporting the omnific-integers article.

This does NOT implement arbitrary surreal numbers or verify the manuscript
in a proof assistant. Symbolic identities are checked over ordinary
polynomial rings. Pell and guard checks cover explicitly finite ranges.

Usage: python verification.py [--output verification_report.json]
Requires: Python 3.9+ and SymPy (tested with the version recorded in output).
"""
from __future__ import annotations

import argparse
import json
import math
import platform
from pathlib import Path
from typing import Dict, List, Tuple, Any

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


def require(condition: bool, description: str) -> None:
    """Raise even when Python is run with optimization (-O)."""
    if not condition:
        raise AssertionError(description)


def zero_polynomial(expr: Any, description: str) -> None:
    require(sp.expand(expr) == 0, description)


def zero_matrix(matrix: Any, description: str) -> None:
    for entry in matrix:
        zero_polynomial(entry, description)


def three_squares(n: int) -> Tuple[int, int, int]:
    """Find a nonnegative three-square representation by finite search."""
    if n < 0:
        raise ValueError("The input must be nonnegative")
    for a in range(math.isqrt(n) + 1):
        rest = n - a * a
        for b in range(math.isqrt(rest) + 1):
            c2 = rest - b * b
            c = math.isqrt(c2)
            if c * c == c2:
                return a, b, c
    raise ValueError(f"No representation as three squares found for {n}")


def pell_pair(k: int) -> Tuple[int, int]:
    if k < 0:
        raise ValueError("Index must be nonnegative")
    u, v = 1, 0
    for _ in range(k):
        u, v = 3 * u + 4 * v, 2 * u + 3 * v
    return u, v


def guard_witness(squared_norm: int) -> Dict[str, Any]:
    """Construct a finite example following the article's residue table."""
    if squared_norm < 0:
        raise ValueError("Squared norm must be nonnegative")
    chosen_residue = (1, 3, 3, 1, 1, 3, 1, 1)[squared_norm % 8]
    k = 0 if chosen_residue == 1 else 1
    while True:
        u, v = pell_pair(k)
        if u > squared_norm:
            break
        k += 2
    w = three_squares(u - squared_norm)
    require(u * u - 2 * v * v == 1, "Pell witness")
    require(u == squared_norm + sum(a * a for a in w), "Square-gap witness")
    require(u % 8 == chosen_residue, "Selected residue")
    return {"squared_norm": squared_norm, "pell_index": k,
            "u": u, "v": v, "w": list(w)}


def run_checks() -> Dict[str, Any]:
    t, s = sp.symbols("t s")
    X, Y, Z, T = sp.symbols("X Y Z T")
    D, E = sp.symbols("D E", positive=True)
    identities: List[str] = []

    # Pythagorean identity and explicit ideal certificate.
    x, y, z = t**2 - 1, 2*t, t**2 + 1
    zero_polynomial(x*x + y*y - z*z, "Pythagorean identity")
    a = t**2 / 2
    zero_polynomial(a*z - (a+1)*x - 1, "Pythagorean Bezout certificate")
    identities += ["Pythagorean identity", "Pythagorean unimodularity certificate"]

    # Hyperboloid identity. The positive assumption on D fixes sqrt(D)^2=D.
    x = 1 + E*t*t/2
    y = E*t*t/(2*sp.sqrt(D))
    z = t
    zero_polynomial(x*x - D*y*y - E*z*z - 1, "Hyperboloid identity")
    zero_polynomial(x - (E*t/2)*z - 1, "Hyperboloid Bezout certificate")
    identities += ["Hyperboloid identity", "Hyperboloid unimodularity certificate"]

    # Cubic norm via a polynomial resultant; no numerical root approximation.
    norm = sp.resultant(T**3 - 2, X + Y*T + Z*T**2, T)
    zero_polynomial(norm - (X**3 + 2*Y**3 + 4*Z**3 - 6*X*Y*Z),
                    "Cubic norm formula")
    identities.append("Cubic norm formula via resultant")

    # Algebra behind the indefinitely continuing Euclidean example.
    alpha = sp.sqrt(2) - 1
    require(sp.simplify(1 - 2*alpha - alpha**2) == 0, "Euclidean remainder ratio")
    identities.append("Euclidean remainder-ratio identity")

    # Finite quadratic-isometry checks for every indefinite signature
    # in dimensions 3 through 7. This supplements, not replaces, the
    # general bilinear proof in the article.
    matrix_cases = []
    for n in range(3, 8):
        for positives in range(1, n):
            signs = [1]*positives + [-1]*(n-positives)
            B = sp.diag(*signs)
            e = sp.zeros(n, 1)
            e[0], e[positives] = 1, 1
            u_index = next(j for j in range(n) if j not in (0, positives))
            u = sp.zeros(n, 1)
            u[u_index] = 1
            N = u*(e.T*B) - e*(u.T*B)
            zero_matrix(N**3, "Nilpotence N^3=0")
            zero_matrix(N.T*B + B*N, "B-skewness")
            Tt = sp.eye(n) + t*N + t*t*N*N/2
            Ts = sp.eye(n) + s*N + s*s*N*N/2
            Tsum = sp.eye(n) + (s+t)*N + (s+t)**2*N*N/2
            zero_matrix(Tt.T*B*Tt - B, "Quadratic-form preservation")
            zero_matrix(Ts*Tt - Tsum, "Additive parameter group law")
            matrix_cases.append({"dimension": n,
                                 "signature": [positives, n-positives]})

    # Pell congruences and recurrence over a finite range.
    pell_samples = []
    for k in range(31):
        u, v = pell_pair(k)
        require(u*u - 2*v*v == 1, f"Pell equation at k={k}")
        require(u % 8 == (1 if k % 2 == 0 else 3), f"Pell residue at k={k}")
        if k >= 2:
            require(u == 6*pell_pair(k-1)[0] - pell_pair(k-2)[0],
                    f"Pell recurrence at k={k}")
        if k <= 5:
            pell_samples.append({"k": k, "u": u, "v": v})

    for residue, u_residue in enumerate((1, 3, 3, 1, 1, 3, 1, 1)):
        require((u_residue-residue) % 8 in {1, 2, 3, 5, 6}, "Residue-table row")

    witnesses = [guard_witness(S) for S in range(256)]
    for witness in witnesses:
        S, u, v = witness["squared_norm"], witness["u"], witness["v"]
        w = witness["w"]
        G = (u*u-2*v*v-1)**2 + (u-S-sum(a*a for a in w))**2
        require(G == 0, "Quartic guard witness")

    return {
        "status": "PASS",
        "scope": "Finite symbolic identities and finite example ranges only; not a formal proof of the article.",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "symbolic_scalar_identities": identities,
        "quadratic_isometry_cases": matrix_cases,
        "quadratic_isometry_case_count": len(matrix_cases),
        "pell_indices_checked": [0, 30],
        "pell_samples": pell_samples,
        "guard_squared_norms_checked": [0, 255],
        "guard_witness_count": len(witnesses),
        "guard_witnesses": witnesses,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_report.json"),
                        help="Destination for the JSON report (default: current directory)")
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS: scalar identities, 20 quadratic-isometry cases, 31 Pell pairs, 256 guard witnesses.")
    print(f"Report: {args.output.resolve()}")
    print("These checks do not constitute formal verification of the manuscript.")


if __name__ == "__main__":
    main()
