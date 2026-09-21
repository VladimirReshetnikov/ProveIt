#!/usr/bin/env python3
"""Exact finite checks for the examples in Surcomplex Analysis.

Requires Python 3.10+ and SymPy. This is formal truncated-series arithmetic,
not an implementation of surreal numbers or a verification of the general
support lemmas and factorization theorems.
"""
from __future__ import annotations

import sys
from typing import Sequence

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

Scalar = sp.Expr


def pad(a: Sequence[Scalar], order: int) -> list[Scalar]:
    """Coefficients through degree order, padded with exact zeros."""
    return [sp.sympify(a[k]) if k < len(a) else sp.S.Zero for k in range(order + 1)]


def add(a: Sequence[Scalar], b: Sequence[Scalar], order: int) -> list[Scalar]:
    aa, bb = pad(a, order), pad(b, order)
    return [sp.expand(x + y) for x, y in zip(aa, bb)]


def mul(a: Sequence[Scalar], b: Sequence[Scalar], order: int) -> list[Scalar]:
    aa, bb = pad(a, order), pad(b, order)
    return [sp.expand(sum(aa[j] * bb[n - j] for j in range(n + 1)))
            for n in range(order + 1)]


def exp_series(a: Sequence[Scalar], order: int) -> list[Scalar]:
    """Formal exponential, using (exp A)' = A' exp A; A(0) must be zero."""
    aa = pad(a, order)
    if aa[0] != 0:
        raise ValueError("This checker requires zero constant term for exponentiation.")
    result = [sp.S.One]
    for n in range(1, order + 1):
        result.append(sp.expand(sum(k * aa[k] * result[n - k]
                                    for k in range(1, n + 1)) / n))
    return result


def polynomial(a: Sequence[Scalar], x: sp.Symbol) -> Scalar:
    return sp.Add(*(coefficient * x**n for n, coefficient in enumerate(a)))


def check_zero(a: Sequence[Scalar], label: str) -> None:
    failures = [(n, sp.simplify(value)) for n, value in enumerate(a)
                if sp.simplify(value) != 0]
    if failures:
        raise AssertionError(f"{label}: first nonzero coefficient {failures[0]}")
    print(f"PASS: {label}")


def main() -> int:
    print("Exact verification for Surcomplex Analysis")
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    print("All arithmetic below is exact; no numerical root approximation is used.\n")
    s, x, t = sp.symbols("s x t")
    order = 16
    root_plus = [sp.S.Zero] + [sp.Rational(n ** (n - 1), 2 ** (n - 1) * sp.factorial(n))
                               * sp.I**n for n in range(1, order + 1)]
    root_minus = [sp.S.Zero] + [sp.Rational(n ** (n - 1), 2 ** (n - 1) * sp.factorial(n))
                                * (-sp.I)**n for n in range(1, order + 1)]
    for root, name in ((root_plus, "plus"), (root_minus, "minus")):
        exponential = exp_series(root, order)
        residual = add(mul(root, root, order),
                       [sp.S.Zero, sp.S.Zero] + exponential, order)
        check_zero(residual, f"{name} Lagrange root solves z^2+s^2 exp(z)=0 through s^{order}")
    print("First six terms of z_plus:", polynomial(root_plus[:7], s))

    # Positive-Hahn-degree preparation, with enough x-jets to protect low orders.
    hahn_order, x_order, safe_x_order = 5, 22, 8
    exponential_x = [sp.S.One / sp.factorial(k) for k in range(x_order + 1)]
    p: dict[int, list[Scalar]] = {1: exponential_x[:2]}
    v: dict[int, list[Scalar]] = {1: pad(exponential_x[2:], x_order)}
    for n in range(2, hahn_order + 1):
        product = [sp.S.Zero] * (x_order + 1)
        for j in range(1, n):
            product = add(product, mul(p[j], v[n-j], x_order), x_order)
        p[n] = [-product[0], -product[1]]
        v[n] = pad([-a for a in product[2:]], x_order)

    assert p[1] == [1, 1]
    assert p[2] == [sp.Rational(-1, 2), sp.Rational(-2, 3)]
    print("PASS: first and second Weierstrass polynomial coefficients match the article")
    for n in range(1, hahn_order + 1):
        coefficient = add(p[n], [sp.S.Zero, sp.S.Zero] + v[n], x_order)
        for j in range(1, n):
            coefficient = add(coefficient, mul(p[j], v[n-j], x_order), x_order)
        expected = exponential_x if n == 1 else [sp.S.Zero] * (x_order + 1)
        residual = [sp.expand(a-b) for a, b in zip(coefficient, expected)]
        check_zero(residual[:safe_x_order+1],
                   f"preparation product at t^{n}, for x^0 through x^{safe_x_order}")

    root_sum = add(root_plus, root_minus, order)
    root_product = mul(root_plus, root_minus, order)
    for n in range(1, hahn_order + 1):
        assert sp.simplify(p[n][0] - root_product[2*n]) == 0
        assert sp.simplify(p[n][1] + root_sum[2*n]) == 0
    check_zero(root_sum[1::2], "root sum contains only even powers of s")
    check_zero(root_product[1::2], "root product contains only even powers of s")
    print(f"PASS: preparation polynomial agrees with (z-z_plus)(z-z_minus) through t^{hahn_order}")
    print("Prepared constant coefficient:", sum(p[n][0]*t**n for n in p))
    print("Prepared linear coefficient:", sum(p[n][1]*t**n for n in p))

    # With a=eta/(2*sqrt(t)), normalized roots are a +/- sqrt(1+a^2).
    a = sp.symbols("a")
    sqrt_jet = sum(sp.binomial(sp.Rational(1, 2), k) * a**(2*k) for k in range(6))
    for sign in (1, -1):
        y = a + sign*sqrt_jet
        residual = sp.Poly(sp.expand(y*y - 2*a*y - 1), a)
        check_zero([residual.nth(k) for k in range(11)],
                   f"multiscale quadratic root, sign {sign:+d}, through a^10")

    epsilon = sp.symbols("epsilon")
    jet_order = 9
    exp_jet = sum(x**j / sp.factorial(j) for j in range(jet_order + 1))
    kernel = sum(epsilon**k * x**(-k-1) for k in range(jet_order + 1))
    residue = sp.expand(exp_jet * kernel).coeff(x, -1)
    expected = sum(epsilon**k / sp.factorial(k) for k in range(jet_order + 1))
    assert sp.expand(residue - expected) == 0
    print(f"PASS: moving-pole Cauchy extraction for exp(z), through epsilon^{jet_order}")
    print("\nALL EXACT CHECKS PASSED")
    print("These checks certify finite example identities, not the general theorems.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
