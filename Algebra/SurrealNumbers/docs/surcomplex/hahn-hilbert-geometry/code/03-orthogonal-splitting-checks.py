#!/usr/bin/env python3
"""Finite exact checks accompanying Hilbert Geometry at Surreal Scales.

Requirements: Python 3.10+ and SymPy. No network access is used.
These are finite identity tests, not verification of the infinite-dimensional
or class-theoretic theorems in the article.
Run: python checks.py
"""
from __future__ import annotations

import itertools
import json
import platform
from pathlib import Path

import sympy as sp

q = sp.Symbol("q", real=True, positive=True)
checks: list[dict[str, str | int]] = []


def assert_zero(matrix: sp.MatrixBase, label: str) -> None:
    """Verify a rational matrix vanishes entry by entry over Q(q)."""
    for i, entry in enumerate(matrix):
        if sp.cancel(entry) != 0:
            raise AssertionError(f"{label}: nonzero entry {i}: {entry}")
    checks.append({"name": label, "status": "PASS"})


def trunc_matrix(matrix: sp.MatrixBase, degree: int) -> sp.Matrix:
    """Taylor truncate a matrix regular at q=0 through the given degree."""
    return sp.Matrix(matrix).applyfunc(
        lambda entry: sp.series(entry, q, 0, degree + 1).removeO().expand()
    )


def valuation(expression: sp.Expr) -> int:
    """The q-adic valuation of a nonzero rational expression over Q(q)."""
    expr = sp.cancel(expression)
    if expr == 0:
        raise ValueError("Zero has infinite valuation, not an integer.")
    numerator, denominator = sp.fraction(expr)
    num_terms = sp.Poly(numerator, q).terms()
    den_terms = sp.Poly(denominator, q).terms()
    return min(m[0] for m, c in num_terms if c) - min(
        m[0] for m, c in den_terms if c
    )


# 1. The direct rotation: exact rational identities and a finite binomial jet.
r = q + q**2
P0 = sp.diag(1, 0)
I2 = sp.eye(2)
P = sp.Matrix([[1, r], [r, r**2]]) / (1 + r**2)
W = P * P0 + (I2 - P) * (I2 - P0)
D = I2 - (P - P0) ** 2
assert_zero(P * P - P, "Graph projection is idempotent")
assert_zero(P.T - P, "Graph projection is self-adjoint")
assert_zero(W.T * W - D, "Direct rotation: W*W=D")
assert_zero(W * W.T - D, "Direct rotation: WW*=D")
assert_zero(W * P0 - P * W, "Direct rotation intertwines projections")
# Here D=(1+r^2)^(-1) I. Its inverse square root is sqrt(1+r^2) I.
degree = 8
binomial_jet = sum(sp.binomial(sp.Rational(1, 2), j) * r**(2 * j)
                   for j in range(degree // 2 + 1))
Ujet = trunc_matrix(W * binomial_jet, degree)
assert_zero(trunc_matrix(Ujet.T * Ujet - I2, degree),
            "Direct rotation is unitary through q^8")
assert_zero(trunc_matrix(Ujet * P0 * Ujet.T - P, degree),
            "Direct rotation conjugates projections through q^8")

# 2. A genuinely coupled rectangular-block Schur reduction.
B = sp.Matrix([[2 + q + q**2]])
C = sp.Matrix([[q, q**2]])
Db = sp.Matrix([[q**2], [q]])
Fb = sp.Matrix([[q**2, q], [0, q**3]])
A = B.row_join(C).col_join(Db.row_join(Fb))
S = Fb - Db * B.inv() * C
L = sp.eye(3)
L[1:3, 0:1] = -Db * B.inv()
R = sp.eye(3)
R[0:1, 1:3] = -B.inv() * C
block_diagonal = sp.zeros(3)
block_diagonal[0:1, 0:1] = B
block_diagonal[1:3, 1:3] = S
assert_zero(L * A * R - block_diagonal, "Coupled Schur identity LAR=diag(B,S)")

# 3. A rank-two 3x3 complex rational matrix: all four Penrose equations.
U = sp.Matrix([[1, 0], [sp.I*q, 1], [q**2, -sp.I*q]])
V = sp.Matrix([[1, sp.I*q, 0], [0, 1, q]])
Ar = U * V
Ar_dagger = V.H * (V * V.H).inv() * (U.H * U).inv() * U.H
assert_zero(Ar * Ar_dagger * Ar - Ar, "Penrose equation A A+ A=A")
assert_zero(Ar_dagger * Ar * Ar_dagger - Ar_dagger, "Penrose equation A+ A A+=A+")
assert_zero((Ar * Ar_dagger).H - Ar * Ar_dagger,
            "Penrose equation (A A+)*=A A+")
assert_zero((Ar_dagger * Ar).H - Ar_dagger * Ar,
            "Penrose equation (A+ A)*=A+ A")

# 4. The exact pole example in the article.
Spole = sp.Matrix([[q**2, q], [0, q**3]])
Sinv = sp.Matrix([[q**-2, -q**-4], [0, q**-3]])
assert_zero(Spole * Sinv - I2, "Pole example: right inverse")
assert_zero(Sinv * Spole - I2, "Pole example: left inverse")
nu1 = min(valuation(z) for z in Spole if z != 0)
nu2 = valuation(Spole.det())
inv_val = min(valuation(z) for z in Sinv if z != 0)
assert (nu1, nu2, inv_val) == (1, 5, -4)
checks.append({"name": "Exact inverse valuation = -(nu_2-nu_1)",
               "status": "PASS", "nu_1": nu1, "nu_2": nu2,
               "inverse_valuation": inv_val})

# 5. Enumerate 125 positive triangular exponent triples.
count = 0
for alpha, beta, gamma in itertools.product(range(1, 6), repeat=3):
    # Exact entries of the inverse have exponents -alpha,
    # beta-alpha-gamma, -gamma. No floating-point evaluation is used.
    actual = min(-alpha, beta - alpha - gamma, -gamma)
    predicted = -(alpha + gamma - min(alpha, beta, gamma))
    if actual != predicted:
        raise AssertionError((alpha, beta, gamma, actual, predicted))
    count += 1
checks.append({"name": "Positive triangular exponent triples",
               "status": "PASS", "cases": count})

result = {
    "article": "Hilbert Geometry at Surreal Scales",
    "python": platform.python_version(),
    "sympy": sp.__version__,
    "checks": checks,
    "summary": f"{len(checks)} checks passed, including {count} exponent triples.",
    "scope": "Finite exact algebra only; not a formal verification of the article."
}
output = Path(__file__).resolve().parent / "verification" / "check_results.json"
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
