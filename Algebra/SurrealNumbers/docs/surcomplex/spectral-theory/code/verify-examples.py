#!/usr/bin/env python3
"""Exact finite checks for Surcomplex Spectral Theory.

Requires Python >= 3.9 and SymPy 1.14.0. No floating-point sampling.
The implemented scalar field is Q(i)(t,u), embedded by
v(t)=(0,1), v(u)=(1,0), ordered lexicographically.
This is not a general Hahn-series or surreal-number implementation.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
import random
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional, Tuple

import sympy as sp

Value = Tuple[int, int]
Valuation = Optional[Value]  # None is positive infinity (the valuation of zero).
t, u = sp.symbols("t u", positive=True)
s, z = sp.symbols("s z")
ZERO: Value = (0, 0)
checks = []
case_records = []


def check(name: str, condition: bool) -> None:
    """Record a passing assertion or fail immediately, even under python -O."""
    if not condition:
        raise AssertionError(name)
    checks.append(name)


def equal(a, b) -> bool:
    """Exact equality for the finite symbolic expressions used in this suite."""
    if isinstance(a, sp.MatrixBase) or isinstance(b, sp.MatrixBase):
        a, b = sp.Matrix(a), sp.Matrix(b)
        return a.shape == b.shape and all(sp.simplify(x) == 0 for x in a - b)
    return sp.simplify(a - b) == 0


def add_value(a: Value, b: Value) -> Value:
    return (a[0] + b[0], a[1] + b[1])


def sub_value(a: Value, b: Value) -> Value:
    return (a[0] - b[0], a[1] - b[1])


def polynomial_lead(expr):
    """Least Hahn monomial, not SymPy's largest polynomial monomial."""
    poly = sp.Poly(expr, u, t, extension=sp.I)
    if poly.is_zero:
        raise ValueError("A nonzero polynomial is required.")
    monomial = min(poly.monoms())
    return tuple(map(int, monomial)), poly.coeff_monomial(monomial)


def valuation(expr) -> Valuation:
    expr = sp.cancel(expr)
    if expr == 0:
        return None
    numerator, denominator = sp.fraction(expr)
    vn, _ = polynomial_lead(numerator)
    vd, _ = polynomial_lead(denominator)
    return sub_value(vn, vd)


def leading_coefficient(expr):
    expr = sp.cancel(expr)
    if expr == 0:
        raise ValueError("Zero has no nonzero leading coefficient.")
    numerator, denominator = sp.fraction(expr)
    _, cn = polynomial_lead(numerator)
    _, cd = polynomial_lead(denominator)
    return sp.cancel(cn / cd)


def matrix_valuation(matrix) -> Valuation:
    vals = [v for entry in matrix if (v := valuation(entry)) is not None]
    return min(vals) if vals else None


def determinantal_values(matrix):
    matrix = sp.Matrix(matrix)
    result = [ZERO]
    for k in range(1, min(matrix.shape) + 1):
        values = []
        for rows in itertools.combinations(range(matrix.rows), k):
            for cols in itertools.combinations(range(matrix.cols), k):
                value = valuation(matrix.extract(rows, cols).det())
                if value is not None:
                    values.append(value)
        result.append(min(values) if values else None)
    return result


def minimum_pivot_scales(matrix):
    """Exact integral row/column elimination; returns valuations, not an SVD."""
    work = sp.MutableDenseMatrix(matrix)
    pivots = []
    for k in range(min(work.shape)):
        candidates = []
        for i in range(k, work.rows):
            for j in range(k, work.cols):
                value = valuation(work[i, j])
                if value is not None:
                    candidates.append((value, i, j))
        if not candidates:
            break
        value, row, col = min(candidates)
        work.row_swap(k, row)
        work.col_swap(k, col)
        pivot = work[k, k]
        for i in range(k + 1, work.rows):
            multiplier = sp.cancel(work[i, k] / pivot)
            for j in range(k + 1, work.cols):
                work[i, j] = sp.cancel(work[i, j] - multiplier * work[k, j])
            work[i, k] = 0
        # Below the pivot is now zero, so clearing its row leaves the
        # trailing Schur block unchanged.
        for j in range(k + 1, work.cols):
            work[k, j] = 0
        pivots.append(value)
    return pivots, sp.Matrix(work)


def verify_profile(name, matrix, expected):
    delta = determinantal_values(matrix)
    pivots, diagonal = minimum_pivot_scales(matrix)
    cumulative = [ZERO]
    for value in expected:
        cumulative.append(add_value(cumulative[-1], value))
    cumulative += [None] * (min(matrix.shape) - len(expected))
    check(name + ": minors", delta == cumulative)
    check(name + ": pivots", pivots == list(expected))
    check(name + ": ordered pivots", pivots == sorted(pivots))
    check(name + ": diagonal result", all(
        equal(diagonal[i, j], 0)
        for i in range(diagonal.rows) for j in range(diagonal.cols) if i != j
    ))
    check(name + ": nonzero diagonal count", sum(x != 0 for x in diagonal.diagonal()) == len(expected))
    case_records.append({"name": name, "shape": list(matrix.shape),
                         "expected_scales": expected, "deltas": delta,
                         "pivot_scales": pivots})


def gram_coefficients(matrix):
    polynomial = sp.Poly(sp.expand((sp.eye(matrix.cols) + s * matrix.H * matrix).det()), s)
    return [sp.expand(polynomial.nth(k)) for k in range(min(matrix.shape) + 1)]


def verify_gram(name, matrix):
    coefficients = gram_coefficients(matrix)
    deltas = determinantal_values(matrix)
    for k, coefficient in enumerate(coefficients):
        sum_squares = sp.Integer(0)
        for rows in itertools.combinations(range(matrix.rows), k):
            for cols in itertools.combinations(range(matrix.cols), k):
                minor = matrix.extract(rows, cols).det()
                sum_squares += sp.conjugate(minor) * minor
        check(name + ": Gram squared minors k=" + str(k), equal(coefficient, sum_squares))
        target = None if deltas[k] is None else add_value(deltas[k], deltas[k])
        check(name + ": Gram valuation k=" + str(k), valuation(coefficient) == target)


def monomial(value: Value):
    return u ** value[0] * t ** value[1]


def unimodular(size: int, rng: random.Random):
    result = sp.eye(size)
    if size == 1:
        return result
    choices = [sp.Integer(1), -sp.Integer(1), sp.I, t, u]
    for _ in range(3):
        i, j = rng.sample(range(size), 2)
        elementary = sp.eye(size)
        elementary[i, j] = rng.choice(choices)
        result = (elementary * result).applyfunc(sp.expand)
    return result


def run_checks():
    check("valuation: lower-rank ordered group", valuation(u / t**20 + t**3) == (0, 3))
    check("valuation: exact cancellation", valuation((1 + t**2) - 1) == (0, 2))
    check("valuation: rational cancellation", valuation((t**2 - 1) / (t - 1)) == ZERO)
    check("valuation: zero sentinel", valuation(t - t) is None)
    check("valuation: complex leading coefficient", equal(leading_coefficient((1 + sp.I)*u/t + u**2), 1 + sp.I))

    near = sp.Matrix([[1, 1], [1, 1 + t**2]])
    examples = [
        ("zero rectangular", sp.zeros(2, 3), []),
        ("identity", sp.eye(2), [ZERO, ZERO]),
        ("nearly dependent", near, [ZERO, (0, 2)]),
        ("rank-one all-ones", sp.ones(2, 2), [ZERO]),
        ("three scales", sp.diag(1, t**2, u), [ZERO, (0, 2), (1, 0)]),
        ("negative scales", sp.diag(t**-2, u/t), [(0, -2), (1, -1)]),
        ("complex rank one", sp.Matrix([[1, sp.I], [sp.I, -1]]), [ZERO]),
    ]
    for name, matrix, expected in examples:
        verify_profile(name, matrix, expected)

    rng = random.Random(20260921)
    available = [(0, -1), ZERO, (0, 1), (0, 2), (1, -1), (1, 0), (2, 0)]
    for index in range(10):
        m, n = [(2, 3), (3, 2), (3, 3)][index % 3]
        rank = index % (min(m, n) + 1)
        scales = sorted(rng.choices(available, k=rank))
        diagonal = sp.zeros(m, n)
        for j, value in enumerate(scales):
            diagonal[j, j] = rng.choice([1, 2, 1 + sp.I]) * monomial(value)
        left, right = unimodular(m, rng), unimodular(n, rng)
        check("generated %d: left determinant" % index, equal(left.det(), 1))
        check("generated %d: right determinant" % index, equal(right.det(), 1))
        matrix = (left * diagonal * right).applyfunc(sp.expand)
        verify_profile("generated %d" % index, matrix, scales)

    verify_gram("near", near)
    verify_gram("complex", sp.Matrix([[1, sp.I], [t, 1]]))
    verify_gram("three-scale diagonal", sp.diag(1, t**2, u))
    verify_gram("rectangular", sp.Matrix([[1, t], [sp.I, 0], [u, 1]]))
    verify_gram("rank deficient", sp.ones(2, 2))
    c = gram_coefficients(near)
    check("near: explicit Gram coefficients", equal(c[1], 4 + 2*t**2 + t**4) and equal(c[2], t**4))
    check("near: leading square first block", equal(leading_coefficient(c[1]), 4))
    check("near: leading square second block", equal(leading_coefficient(c[2])/leading_coefficient(c[1]), sp.Rational(1, 4)))
    c = gram_coefficients(sp.diag(2*t, 3*t))
    residual = z**2 - leading_coefficient(c[1])*z + leading_coefficient(c[2])
    check("equal-scale residual polynomial", equal(residual, (z-4)*(z-9)))

    a = sp.Matrix([[1, t], [0, 0]])
    ad = sp.Matrix([[1, 0], [t, 0]]) / (1+t**2)
    check("Penrose ABA=A", equal(a*ad*a, a))
    check("Penrose BAB=B", equal(ad*a*ad, ad))
    check("Penrose AB Hermitian", equal((a*ad).H, a*ad))
    check("Penrose BA Hermitian", equal((ad*a).H, ad*a))

    h = sp.diag(0, t**2)
    b = t**2/sp.Integer(2) * sp.Matrix([[1, -1], [-1, 1]])
    p = sp.diag(1, 0)
    q = sp.Matrix([[1, 1], [1, 1]]) / 2
    check("rotation: identical spectra", equal((z*sp.eye(2)-h).det(), (z*sp.eye(2)-b).det()))
    check("rotation: projectors", equal(p*p, p) and equal(q*q, q) and equal(b*q, sp.zeros(2)))
    check("rotation: error squared", equal((b-h)**2, t**4/2*sp.eye(2)))
    check("rotation: projector difference squared", equal((p-q)**2, sp.eye(2)/2))
    check("rotation: Frobenius difference squared", equal(sp.trace((p-q).H*(p-q)), 1))

    ht = sp.Matrix([[0, t], [t, 1]])
    low = (1-sp.sqrt(1+4*t**2))/2
    high = (1+sp.sqrt(1+4*t**2))/2
    check("second order: eigenvalue", equal(low**2-low-t**2, 0))
    projector = (high*sp.eye(2)-ht)/(high-low)
    check("second order: spectral projector", equal(projector**2, projector))
    check("second order: projector eigenidentity", equal(ht*projector, low*projector))
    expansion = -t**2+t**4-2*t**6+5*t**8
    check("second order: expansion", equal(sp.series(low, t, 0, 10).removeO(), expansion))
    check("second order: residual valuation", valuation(expansion**2-expansion-t**2) == (0, 10))
    check("Schur complement: characteristic equation", equal((1-z)*(-z-t**2/(1-z)), (ht-z*sp.eye(2)).det()))
    rank_one = sp.Matrix([[t**2, t], [t, 1]])
    check("Schur complement: exact rank loss", rank_one.det() == 0 and rank_one.rank() == 1)

    nilpotent = sp.Matrix([[0, 1], [0, 0]])
    error = sp.Matrix([[0, 0], [t**2, 0]])
    check("pseudospectrum: exact eigenvalue shift", equal((z*sp.eye(2)-nilpotent-error).det(), z**2-t**2))
    verify_profile("pseudospectral resolvent", t*sp.eye(2)-nilpotent, [ZERO, (0, 2)])

    e = sp.Matrix([[t, u], [0, t**2]])
    partial = sum((e**k for k in range(5)), sp.zeros(2))
    check("finite Neumann identity", equal((sp.eye(2)-e)*partial, sp.eye(2)-e**5))
    hermitian_e = t*sp.Matrix([[1, sp.I], [-sp.I, 2]])
    root_partial = sum((sp.binomial(sp.Rational(1, 2), k)*hermitian_e**k for k in range(5)), sp.zeros(2))
    remainder = root_partial**2-sp.eye(2)-hermitian_e
    check("finite binomial residual scale", matrix_valuation(remainder) == (0, 5))
    check("finite binomial Hermitian", equal(root_partial.H, root_partial))

    alpha = t**2
    regularized = t/(t**2+alpha**2)
    check("regularization: exact solution", equal(regularized, 1/(t*(1+t**2))))
    check("regularization: infinite output scale", valuation(regularized) == (0, -1))
    check("regularization: boundary attenuation", equal((2*t)**2/((2*t)**2+(3*t)**2), sp.Rational(4, 13)))
    check("Schmidt: normalized vector", equal(1/(1+t**2)+t**2/(1+t**2), 1))
    check("Schmidt: hidden weight scale", valuation(t**2/(1+t**2)) == (0, 2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent.parent / "data")
    args = parser.parse_args()
    run_checks()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    report = {
        "status": "PASS",
        "assertions_passed": len(checks),
        "profile_cases": len(case_records),
        "seed": 20260921,
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "run_utc": datetime.now(timezone.utc).isoformat(),
        "field": "Q(i)(t,u); v(t)=(0,1), v(u)=(1,0), lexicographic order",
        "scope": "Exact finite examples and test matrices only; not formal verification of the article's general theorems or arbitrary Hahn support calculus.",
        "assertions": checks,
        "profile_case_details": case_records,
    }
    (args.output_dir / "verification_report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    text = ("PASS: %d exact assertions; %d matrix-profile cases.\n"
            "Python %s; SymPy %s.\n"
            "No floating-point sampling.\n"
            "This is finite-example verification, not a proof-assistant check.\n"
            % (len(checks), len(case_records), platform.python_version(), sp.__version__))
    (args.output_dir / "verification_report.txt").write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
