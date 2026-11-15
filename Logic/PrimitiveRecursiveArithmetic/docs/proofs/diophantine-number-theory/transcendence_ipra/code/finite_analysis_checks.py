#!/usr/bin/env python3
"""Representative exact checks for the finite analytic compilation.

Dependency: SymPy. Run from any directory with Python 3.
These finite examples validate formulas and signs; they are not general
proofs and do not certify derivability in iPRA or Lean.
"""

from fractions import Fraction
from math import factorial
import json

import sympy as sp


X, T = sp.symbols("X T")


def e_name(s: int) -> Fraction:
    return sum((Fraction(1, factorial(j)) for j in range(s + 2)), Fraction())


def atan_name(b: int, s: int) -> Fraction:
    return sum((Fraction((-1) ** j, (2 * j + 1) * b ** (2 * j + 1))
                for j in range(s + 1)), Fraction())


def pi_name(s: int) -> Fraction:
    return 16 * atan_name(5, s) - 4 * atan_name(239, s)


def matrix_poly(poly: sp.Poly, b: sp.Matrix) -> sp.Matrix:
    out = sp.zeros(b.rows)
    for coefficient in poly.all_coeffs():
        out = out * b + coefficient * sp.eye(b.rows)
    return out


def exp_cut(b: sp.Matrix, order: int) -> sp.Matrix:
    return sum((b**j / factorial(j) for j in range(order + 1)), sp.zeros(b.rows))


def integrate_matrix(b: sp.Matrix) -> sp.Matrix:
    return b.applyfunc(lambda entry: sp.integrate(entry, (T, 0, 1)))


def max_row_sum(b: sp.Matrix) -> sp.Expr:
    return max(sum(abs(b[i, j]) for j in range(b.cols)) for i in range(b.rows))


def finite_hermite_check(b: sp.Matrix, f: sp.Poly, order: int) -> dict:
    F = sp.Poly(sum(sp.diff(f.as_expr(), X, r)
                    for r in range(f.degree() + 1)), X)
    assert sp.expand(sp.diff(F.as_expr(), X) - F.as_expr() + f.as_expr()) == 0
    lhs = exp_cut(b, order) * F.nth(0) - matrix_poly(F, b)
    integral = integrate_matrix(
        exp_cut((1 - T) * b, order) * b * matrix_poly(f, T * b)
    )
    defect = b ** (order + 1) / factorial(order) * integrate_matrix(
        (1 - T) ** order * matrix_poly(F, T * b)
    )
    defect_coefficients = sum((
        F.nth(j) * b ** (order + 1 + j) * factorial(j)
        / factorial(order + j + 1)
        for j in range(F.degree() + 1)
    ), sp.zeros(b.rows))
    assert (lhs - integral + defect).applyfunc(sp.simplify) == sp.zeros(b.rows)
    assert (defect - defect_coefficients).applyfunc(sp.simplify) == sp.zeros(b.rows)
    R = max_row_sum(b)
    V = sum(abs(F.nth(j)) * R**j for j in range(F.degree() + 1))
    assert max_row_sum(defect) <= V * R ** (order + 1) / factorial(order + 1)
    return {
        "dimension": b.rows,
        "polynomial": str(f.as_expr()),
        "Taylor_order": order,
        "exact_finite_identity": True,
        "beta_coefficient_identity": True,
        "defect_bound": True,
    }


def main() -> None:
    gaussian_identity = sp.expand((12 + 5 * sp.I) ** 4 - sp.I * (28560 + 239 * sp.I))
    assert gaussian_identity == 0
    r5 = (5 + sp.I) / (5 - sp.I)
    r239 = (239 + sp.I) / (239 - sp.I)
    assert sp.simplify(r5**4 / r239 - sp.I) == 0
    assert sp.simplify(r5**8 / r239**2 + 1) == 0

    cauchy_pairs = 0
    for s in range(8):
        for later in range(s, 13):
            assert abs(e_name(later) - e_name(s)) <= Fraction(1, 2**s)
            assert abs(pi_name(later) - pi_name(s)) <= Fraction(1, 2**s)
            cauchy_pairs += 1
        assert 2 <= e_name(s) < 3
        assert 3 < pi_name(s) < 4

    tail_checks = 0
    for R in range(1, 5):
        for s in range(7):
            L = 4 * (R + 1)**2 + s + 4
            tail = sum((Fraction(R**j, factorial(j))
                        for j in range(L + 1, L + 16)), Fraction())
            assert tail <= Fraction(1, 2**s)
            tail_checks += 1

    examples = [
        (sp.Matrix([[sp.Rational(1, 2)]]), sp.Poly(X**3 / 2 + X, X)),
        (sp.Matrix([[0, 1], [-2, 1]]), sp.Poly(X**3 * (X**2 + 1) / 2, X)),
    ]
    hermite_checks = [finite_hermite_check(b, f, L)
                      for b, f in examples for L in [0, 1, 4]]
    print(json.dumps({
        "status": "all exact checks passed",
        "sympy_version": sp.__version__,
        "Machin_Gaussian_identity": True,
        "rational_name_Cauchy_pairs": cauchy_pairs,
        "finite_exponential_tail_checks": tail_checks,
        "finite_Hermite_checks": hermite_checks,
        "scope": "Representative finite checks; no general iPRA or Lean proof is asserted.",
    }, indent=2))


if __name__ == "__main__":
    main()
