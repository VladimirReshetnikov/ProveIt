#!/usr/bin/env python3
"""Exact finite checks for the examples in surcomplex_analysis.tex.

Requires Python 3 and SymPy. These checks do not verify infinite-support
summability, class-theoretic assertions, or the general analytic theorems.
Run: python verify_examples.py
"""
from __future__ import annotations

import sys
import sympy as sp


def trunc(expr: sp.Expr, var: sp.Symbol, order: int) -> sp.Expr:
    """Return the Taylor polynomial with exponents strictly below order."""
    return sp.expand(sp.series(expr, var, 0, order).removeO())


def require_zero(expr: sp.Expr, message: str) -> None:
    value = sp.simplify(expr)
    if value != 0:
        raise AssertionError(f"{message}: nonzero residual {value}")


def check_euler() -> None:
    x = sp.Symbol("x")
    order = 14
    a = sum(sp.factorial(n) * x**n for n in range(order + 1))
    residual = x**2 * sp.diff(a, x) + (x - 1) * a + 1
    require_zero(trunc(residual, x, order + 1), "Euler differential identity")
    print(f"PASS Euler factorial series: identity through degree {order}.")


def check_lagrange() -> None:
    u = sp.Symbol("u")
    order = 9
    w = sum(sp.Rational((-n)**(n - 1), sp.factorial(n)) * u**n
            for n in range(1, order))
    require_zero(trunc(w * sp.exp(w) - u, u, order), "Lambert inverse")
    print(f"PASS Lagrange inverse W(u) exp(W(u)) = u through degree {order-1}.")
    print("     W(u) =", w)


def check_split_roots() -> None:
    s = sp.Symbol("s")
    for sign in (1, -1):
        z = (sign * sp.I * s - s**2 / 2 - sign * 3 * sp.I * s**3 / 8
             + s**4 / 3 + sign * 125 * sp.I * s**5 / 384)
        residual = trunc(z**2 + s**2 * sp.exp(z), s, 7)
        require_zero(residual, "Split root expansion")
    print("PASS both displayed roots of z^2 + s^2 exp(z): residual O(s^7).")


def check_preparation() -> None:
    z, tau = sp.symbols("z tau")
    # Compute enough z-coefficients to avoid division truncation affecting
    # the first four displayed z-coefficients of the factorization.
    ez = trunc(sp.exp(z), z, 12)
    r1 = 1 + z
    q1 = sp.cancel((ez - r1) / z**2)
    h2 = sp.expand(-r1 * q1)
    r2 = trunc(h2, z, 2)
    q2 = sp.cancel((h2 - r2) / z**2)
    require_zero(r2 + sp.Rational(1, 2) + sp.Rational(2, 3) * z,
                 "Second preparation remainder")
    p = z**2 + tau * r1 + tau**2 * r2
    unit = 1 + tau * q1 + tau**2 * q2
    residual = trunc(trunc(p * unit - (z**2 + tau * ez), tau, 3), z, 6)
    require_zero(residual, "Weierstrass preparation identity")
    print("PASS Weierstrass preparation through tau^2 and z^5.")
    print("     r1(z) =", r1)
    print("     r2(z) =", r2)


def check_quadratic() -> None:
    q = sp.Symbol("q")
    plus = 1 + q - q**2 + 2*q**3 - 5*q**4
    minus = -q + q**2 - 2*q**3 + 5*q**4
    require_zero(trunc(plus**2 - plus - q, q, 5), "Positive quadratic root")
    require_zero(trunc(minus**2 - minus - q, q, 5), "Negative quadratic root")
    require_zero(plus + minus - 1, "Quadratic root sum")
    require_zero(trunc(plus*minus + q, q, 5), "Quadratic root product")
    print("PASS separated-scale quadratic: normalized roots through q^4.")


def check_ramification() -> None:
    z = sp.Symbol("z")
    rational = z**3 / (z**2 + 1)
    derivative = sp.cancel(sp.diff(rational, z))
    num, den = sp.fraction(derivative)
    require_zero(sp.factor(num) - z**2 * (z**2 + 3), "Critical numerator")
    # Poles at +/-i are simple; infinity has local degree 1.
    d = 3
    total_ramification = sp.degree(num, z)
    if total_ramification != 2*d - 2:
        raise AssertionError("Rational ramification count")
    print("PASS R(z)=z^3/(z^2+1): ramification weights 2+1+1=4=2d-2.")


def main() -> None:
    print("Exact symbolic checks for Surcomplex Analysis")
    print("Python", sys.version.split()[0], "| SymPy", sp.__version__)
    print("These finite checks are not a formal verification of the general proofs.\n")
    check_euler()
    check_lagrange()
    check_split_roots()
    check_preparation()
    check_quadratic()
    check_ramification()
    print("\nAll six exact checks passed.")


if __name__ == "__main__":
    main()
