#!/usr/bin/env python3
"""Exact diagnostics for the degree theorem and shorter-stencil hierarchy.

These are executable algebra checks, not substitutes for the analytic proofs.
Only SymPy and the Python standard library are required.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
N, x = sp.symbols("N x", integer=True)
records: list[dict] = []


def check(name, expression):
    value = sp.factor(expression)
    if value != 0:
        raise AssertionError(f"{name}: nonzero difference {value}")
    records.append({"name": name, "status": "passed"})


def harmonic_decomposition(r, residues):
    """Exact decomposition for integer poles (a,h,c), based at a=1.

    Each residue represents c/(n+a)^h, and a is a positive integer.
    The method expands n^k=((n+a)-a)^k and sums polynomial parts.
    It does not use a determinant or a rank assumption.
    """
    max_order = max(order for _, order, _ in residues)
    moments = []
    coeff = [[sp.Integer(0)] * (2 * r - 1) for _ in range(max_order)]
    n = sp.symbols("n", integer=True, nonnegative=True)
    for k in range(2 * r - 1):
        remainder = sp.Integer(0)
        for a, order, residue in residues:
            for ell in range(k + 1):
                factor = residue * sp.binomial(k, ell) * (-a) ** (k - ell)
                power = ell - order
                if power >= 0:
                    remainder += factor * sp.summation((n + a) ** power, (n, 0, N))
                else:
                    q = -power
                    coeff[q - 1][k] += factor
                    boundary = sum(
                        (N + 1 + j) ** (-q) - sp.Rational(1, j**q)
                        for j in range(1, a)
                    )
                    remainder += factor * boundary
        moments.append(sp.factor(remainder))
    D = sp.Matrix(r, r, lambda i, j: moments[i + j])
    C = [sp.Matrix(r, r, lambda i, j: coeff[q][i + j]) for q in range(max_order)]
    return D, C


def direct_matrix(r, cutoff, residues):
    return sp.Matrix(
        r,
        r,
        lambda i, j: sum(
            sum(c * sp.Rational(1, (n + a) ** h) for a, h, c in residues)
            * n ** (i + j)
            for n in range(cutoff + 1)
        ),
    )


# The two exact examples in the article, using independent finite moments.
for tag, c in [("positive", sp.Integer(1)), ("signed", -sp.Rational(7, 5))]:
    residues = [(1, 1, sp.Integer(1)), (2, 1, c)]
    D, C_list = harmonic_decomposition(3, residues)
    C = C_list[0]
    assert C.rank() == 2
    K = sp.Matrix([2, 3, 1])
    if C * K != sp.zeros(3, 1):
        raise AssertionError(f"{tag}: incorrect kernel")
    records.append({"name": f"{tag}: kernel", "status": "passed"})
    compression = sp.factor((K.T * D * K)[0])
    polynomial = sp.Poly((D + x * C).det(), x)
    check(f"{tag}: compressed top coefficient", polynomial.coeff_monomial(x**2) - C[:2, :2].det() * compression)
    for cutoff in [0, 1, 2, 4, 9]:
        H = sp.harmonic(cutoff + 1)
        lhs = D.subs(N, cutoff) + H * C
        rhs = direct_matrix(3, cutoff, residues)
        assert lhs == rhs
        records.append({"name": f"{tag}: direct moments N={cutoff}", "status": "passed"})
    if tag == "positive":
        check("positive exact leading", polynomial.coeff_monomial(x**2) - (N + 1) * (N + 2) ** 2 * (N + 3) / 2)
    else:
        check("signed exact compression", compression + (N - 2) * (N + 1) * (N + 2) * (N + 3) / 10)
        check("signed exact leading", polynomial.coeff_monomial(x**2) - 7 * (N - 2) * (N + 1) * (N + 2) * (N + 3) / 50)
        check("signed exceptional polynomial", polynomial.as_expr().subs(N, 2) - (620 * x - 1137) / 500)
        check("signed direct determinant", direct_matrix(3, 2, residues).det() + sp.Rational(1, 1500))


# Generic kernel isotropy for the non-common-kernel rank-two Hankel pencil.
# This is deliberately not a pencil whose coefficients have one fixed kernel.
u, v = sp.symbols("u v")
C = sp.Matrix([[0, u, 0], [u, 0, v], [0, v, 0]])
K = sp.Matrix([v, 0, -u])
assert C.rank() == 2
assert sp.Matrix.hstack(*C.subs({u: 1, v: 0}).nullspace(), *C.subs({u: 0, v: 1}).nullspace()).rank() == 2
for letter in [u, v]:
    check(f"varying-kernel isotropy {letter}", (K.T * C.diff(letter) * K)[0])


# Every critical rank, with exact residue matrices formed independently by
# rational partial fractions rather than the spectral moment formula.
hierarchy_cases = []
for r in range(2, 7):
    for rho in range(1, r + 1):
        h = 2 * r - rho - 1
        residues = [
            (1 + j, rho, (-1) ** j * sp.binomial(h, j) / sp.factorial(h))
            for j in range(h + 1)
        ]
        # Avoid symbolic N summation here: the residues alone determine C_q.
        matrices = []
        for q in range(1, rho + 1):
            values = []
            for k in range(2 * r - 1):
                ell = rho - q
                value = 0 if ell > k else sum(
                    c * sp.binomial(k, ell) * (-a) ** (k - ell)
                    for a, _, c in residues
                )
                values.append(sp.factor(value))
            matrices.append(sp.Matrix(r, r, lambda i, j: values[i + j]))
        X = sp.symbols(f"X1:{rho + 1}")
        pencil = sum((X[q] * matrices[q] for q in range(rho)), sp.zeros(r))
        L = r - rho
        assert all(pencil[i, j] == 0 for i in range(L) for j in range(r))
        target = (-1) ** (rho * (rho - 1) // 2) * X[-1] ** rho
        check(f"critical rank block r={r},rho={rho}", pencil[L:, L:].det() - target)
        hierarchy_cases.append({"r": r, "rho": rho, "h": h, "rank": rho})


# The two-particle closure is checked from separately constructed moments.
a, A, z0, z1 = sp.symbols("a A z0 z1")
moment = sp.Matrix([[A, z0 - A], [z0 - A, 2 * z1 - (2 * a + 1) * z0 + A]])
closed = 2 * A * z1 + (1 - 2 * a) * A * z0 - z0**2
check("r2 rho2 closure", moment.det() - closed)


# Independent formal Laurent multiplication: the next Stieltjes coefficient
# contributes through the square of the pole.
t, g0, g1, g2, loga = sp.symbols("t g0 g1 g2 loga")
zeta1 = 1 / t + g0 - g1 * t + g2 * t**2 / 2
alpha = (1 - loga * t + loga**2 * t**2 / 2) / a
zeta0_constant = sp.Rational(1, 2) - a
local = 2 * alpha * zeta0_constant + (1 - 2 * a) * alpha * zeta1 - zeta1**2
c = 1 / a - 2
check("r2 double-pole coefficient", sp.expand(local).coeff(t, -2) + 1)
check("r2 residue coefficient", sp.expand(local).coeff(t, -1) - (c - 2 * g0))
check("r2 Stieltjes finite part", sp.expand(local).coeff(t, 0) - (2 * g1 - g0**2 + c * (g0 - loga + 1)))


result = {
    "status": "passed",
    "sympy_version": sp.__version__,
    "checks": records,
    "hierarchy_cases": hierarchy_cases,
    "scope": "Exact algebra diagnostics; analytic proofs are in the article.",
}
(HERE / "exact_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"Passed {len(records)} exact checks; {len(hierarchy_cases)} critical hierarchy cases.")
