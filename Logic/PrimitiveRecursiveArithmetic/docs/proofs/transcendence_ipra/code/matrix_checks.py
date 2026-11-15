#!/usr/bin/env python3
"""Exact finite checks for the root-free Hermite matrix argument.

Run: python3 code/matrix_checks.py
Dependency: SymPy >= 1.12 (tested with 1.14.0).

This checks representative finite identities using exact rational arithmetic.
It is not a proof of the general identities or a completed iPRA/Lean proof.
No numerical approximation to pi, e, or a matrix exponential is used.
"""

from __future__ import annotations

from itertools import combinations
from math import factorial, gcd, lcm
import json

import sympy as sp


X, T, Z = sp.symbols("X T Z")


def additive_compound(a: sp.Matrix, r: int) -> sp.Matrix:
    """The action of A on the rth exterior power, in increasing-subset bases."""
    n = a.rows
    assert a.cols == n and 0 <= r <= n
    basis = list(combinations(range(n), r))
    positions = {item: index for index, item in enumerate(basis)}
    out = sp.zeros(len(basis))
    for col, subset in enumerate(basis):
        for slot, old in enumerate(subset):
            for new in range(n):
                wedge = list(subset)
                wedge[slot] = new
                if len(set(wedge)) < r:
                    continue
                inversions = sum(
                    wedge[i] > wedge[j]
                    for i in range(r)
                    for j in range(i + 1, r)
                )
                row = positions[tuple(sorted(wedge))]
                out[row, col] += (-1) ** inversions * a[new, old]
    return out


def multiplicative_compound(a: sp.Matrix, r: int) -> sp.Matrix:
    """The rth exterior power of A: its entries are r-by-r minors."""
    basis = list(combinations(range(a.rows), r))
    if r == 0:
        return sp.ones(1)
    return sp.Matrix([
        [a.extract(rows, cols).det() for cols in basis]
        for rows in basis
    ])


def exterior_sum(a: sp.Matrix) -> sp.Matrix:
    return sp.diag(*(additive_compound(a, r) for r in range(a.rows + 1)))


def exp_trunc(a: sp.Matrix, order: int) -> sp.Matrix:
    out = sp.zeros(a.rows)
    power = sp.eye(a.rows)
    for j in range(order + 1):
        out += power * T**j / factorial(j)
        power = power * a
    return out


def coeff(value: sp.Expr, j: int) -> sp.Expr:
    return sp.Poly(sp.expand(value), T).nth(j)


def companion(poly: sp.Poly) -> sp.Matrix:
    """Transpose companion, matching the column (1,z,...,z^(n-1))."""
    assert poly.LC() == 1
    n = poly.degree()
    out = sp.zeros(n)
    for j in range(n - 1):
        out[j, j + 1] = 1
    for j in range(n):
        out[n - 1, j] = -poly.nth(j)
    return out


def zero_factor(poly: sp.Poly) -> tuple[int, sp.Poly]:
    k = next(j for j in range(poly.degree() + 1) if poly.nth(j) != 0)
    return k, sp.Poly(poly.as_expr() / X**k, X)


def matrix_poly(poly: sp.Poly, a: sp.Matrix) -> sp.Matrix:
    """Exact Horner evaluation, including the empty-matrix convention."""
    out = sp.zeros(a.rows)
    identity = sp.eye(a.rows)
    for term in poly.all_coeffs():
        out = out * a + term * identity
    return out


def check_exterior_identities(a: sp.Matrix, order: int = 5) -> dict:
    b = exterior_sum(a)
    assert b.rows == 2**a.rows
    assert b[0, 0] == 0
    u = exp_trunc(a, order)
    lhs = sp.expand((sp.eye(a.rows) + u).det())
    rhs = sp.trace(exp_trunc(b, order))
    for j in range(order + 1):
        assert coeff(lhs - rhs, j) == 0, (a, j)
    for r in range(a.rows + 1):
        lhs_r = multiplicative_compound(u, r)
        rhs_r = exp_trunc(additive_compound(a, r), order)
        for entry in lhs_r - rhs_r:
            for j in range(order + 1):
                assert coeff(entry, j) == 0, (a, r, j)
    return {"dimension": a.rows, "exterior_dimension": b.rows, "order": order}


def hermite_data(b: sp.Matrix, p: int) -> dict:
    c = lcm(*(int(sp.denom(entry)) for entry in b))
    mtx = c * b
    chi = sp.Poly(mtx.charpoly(X).as_expr(), X)
    k, g = zero_factor(chi)
    assert k >= 1
    assert g.LC() == 1 and g.nth(0) != 0
    assert all(entry.is_Integer for entry in mtx)
    assert gcd(p, k * c * abs(int(g.nth(0)))) == 1
    assert p >= 2
    h = sp.Poly(X ** (p - 1) * g.as_expr() ** p, X)
    ell = h.degree()
    comp = companion(g)
    assert matrix_poly(g, comp) == sp.zeros(comp.rows)
    # Newton traces, checked past every power needed by the Hermite polynomial.
    powers_m = [sp.eye(mtx.rows)]
    powers_c = [sp.eye(comp.rows)]
    for j in range(1, ell + 1):
        powers_m.append(powers_m[-1] * mtx)
        powers_c.append(powers_c[-1] * comp)
        assert sp.trace(powers_m[j]) == sp.trace(powers_c[j])
    traces_m = [sp.trace(value) for value in powers_m]
    traces_c = [sp.trace(value) for value in powers_c]
    assert traces_m[0] - traces_c[0] == k

    s = sp.Rational(0)
    f0 = sp.Rational(0)
    sc = sp.Rational(0)
    denom = factorial(p - 1)
    derivative = h
    for r in range(ell + 1):
        scale = sp.Rational(c**r, denom)
        at_m_trace = scale * sum(
            derivative.nth(j) * traces_m[j]
            for j in range(derivative.degree() + 1)
        )
        at_c_trace = scale * sum(
            derivative.nth(j) * traces_c[j]
            for j in range(derivative.degree() + 1)
        )
        at_zero = scale * derivative.nth(0)
        assert at_m_trace == k * at_zero + at_c_trace
        if r < p:
            assert sp.rem(derivative, g).is_zero
            assert at_c_trace == 0
        else:
            assert all(
                (scale * value).is_Integer and int(scale * value) % p == 0
                for value in derivative.all_coeffs()
            )
        s += at_m_trace
        f0 += at_zero
        sc += at_c_trace
        derivative = derivative.diff()
    assert s.is_Integer and f0.is_Integer and sc.is_Integer
    s, f0, sc = int(s), int(f0), int(sc)
    expected = k * pow(c, p - 1, p) * pow(int(g.nth(0)), p, p) % p
    assert expected != 0
    assert s % p == expected
    assert sc % p == 0
    assert s == k * f0 + sc
    assert f0 % p == pow(c, p - 1, p) * pow(int(g.nth(0)), p, p) % p
    return {
        "dimension": b.rows,
        "denominator": c,
        "zero_multiplicity": k,
        "nonzero_factor": str(g.as_expr()),
        "modulus": p,
        "modulus_is_composite": not bool(sp.isprime(p)),
        "auxiliary_degree": ell,
        "nonzero_residue": expected,
        "trace_integer_digits": len(str(abs(s))),
    }


def check_q_transform(poly: sp.Poly) -> dict:
    even = sum((poly.nth(2 * j) * X**j for j in range(poly.degree() // 2 + 1)), sp.Integer(0))
    odd = sum((poly.nth(2 * j + 1) * X**j for j in range((poly.degree() + 1) // 2)), sp.Integer(0))
    q = sp.Poly(
        sp.expand(even.subs(X, -Z**2) ** 2 + Z**2 * odd.subs(X, -Z**2) ** 2), Z
    )
    assert sp.expand(q.as_expr() - poly.as_expr().subs(X, -sp.I * Z)
                     * poly.as_expr().subs(X, sp.I * Z)) == 0
    assert sp.expand(q.as_expr().subs(Z, sp.I * X)
                     - poly.as_expr() * poly.as_expr().subs(X, -X)) == 0
    assert q.degree() == 2 * poly.degree()
    assert q.LC() == poly.LC() ** 2
    assert all(item.is_Integer for item in q.all_coeffs())
    if poly.degree() > 0:
        qx = sp.Poly(q.as_expr().subs(Z, X), X)
        a = companion(sp.Poly(qx.as_expr() / qx.LC(), X))
        vector = sp.Matrix([Z**j for j in range(a.rows)])
        residual = a * vector - Z * vector
        assert all(sp.expand(residual[j]) == 0 for j in range(a.rows - 1))
        assert sp.expand(residual[-1] + q.as_expr() / q.LC()) == 0
    return {"P": str(poly.as_expr()), "Q": str(q.as_expr())}


def main() -> None:
    exterior = [
        check_exterior_identities(sp.Matrix([[2]])),
        check_exterior_identities(sp.Matrix([[0, 1], [-2, 3]])),
        check_exterior_identities(sp.Matrix([[1, 2, 0], [0, -1, 1], [2, 0, 1]]), 4),
        check_exterior_identities(sp.Matrix([[0, sp.Rational(1, 2)], [-3, 1]])),
    ]
    q_transforms = [
        check_q_transform(sp.Poly(expr, X))
        for expr in [7, X, X - 3, X**2 + X + 1, 2 * X**3 - 3 * X + 4]
    ]
    samples = [
        (sp.diag(0, 1), [5, 9, 25]),
        (sp.Matrix([[0, 1, 0], [0, 0, 0], [0, 0, 2]]), [5, 25]),
        (sp.diag(0, sp.Rational(1, 2), -sp.Rational(1, 2)), [5, 9]),
        (sp.Matrix([[0, 1], [0, 0]]), [9]),
        (exterior_sum(sp.Matrix([[0, 1], [-9, 0]])), [5, 25]),
    ]
    hermite = [hermite_data(b, p) for b, moduli in samples for p in moduli]
    # A small exact check of the polynomial telescoping identity behind (1).
    test_f = sp.Poly((X**2 + 1) * X**3 / factorial(3), X)
    test_F = sum(sp.diff(test_f.as_expr(), X, r) for r in range(test_f.degree() + 1))
    assert sp.expand(sp.diff(test_F, X) - test_F + test_f.as_expr()) == 0
    print(json.dumps({
        "status": "all exact checks passed",
        "sympy_version": sp.__version__,
        "exterior_power_checks": exterior,
        "integer_polynomial_transforms": q_transforms,
        "hermite_trace_checks": hermite,
        "scope": "Finite validation examples, not a replacement for the general proofs.",
    }, indent=2))


if __name__ == "__main__":
    main()
