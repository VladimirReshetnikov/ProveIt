#!/usr/bin/env python3
"""Exact finite checks for the examples in surcomplex_analysis.tex.

Requires Python 3.10+ and SymPy. Run:
    python verify_examples.py

These checks concern polynomial identities and truncated formal series, not a
machine-checked proof of Hahn summability or any theorem about proper classes.
No floating-point approximations or external services are used.
"""
from __future__ import annotations

import sys
from collections.abc import Callable

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


def truncate(expression: sp.Expr, variable: sp.Symbol, order: int) -> sp.Expr:
    """Return the Taylor polynomial modulo variable**order."""
    return sp.expand(sp.series(expression, variable, 0, order).removeO())


def assert_zero(expression: sp.Expr, description: str) -> None:
    reduced = sp.cancel(sp.expand(expression))
    if reduced != 0:
        raise AssertionError(f"{description}: nonzero residual {reduced}")


def check_catalan_inverse() -> str:
    w, a = sp.symbols("w a")
    order = 12
    inverse = sum((-1) ** (n - 1) * sp.catalan(n - 1) * a ** (n - 1) * w ** n
                  for n in range(1, order))
    assert_zero(truncate(inverse + a * inverse ** 2 - w, w, order),
                "Catalan right inverse")
    x = sp.Symbol("x")
    assert_zero(truncate(inverse.subs(w, x + a * x ** 2) - x, x, order),
                "Catalan left inverse")
    return "Both inverse compositions hold modulo degree 12, with symbolic coefficient a."


def check_factorial_ode() -> str:
    x = sp.Symbol("x")
    order = 18
    euler = sum(sp.factorial(n) * x ** n for n in range(order))
    residual = x ** 2 * sp.diff(euler, x) + (x - 1) * euler + 1
    assert_zero(truncate(residual, x, order), "Factorial-series ODE")
    return "X^2 E' + (X-1)E = -1 holds modulo X^18."


def check_cubic_roots() -> str:
    q = sp.Symbol("q")
    for sign in (-1, 1):
        root = (sign * q + q ** 4 / 2 + sign * sp.Rational(5, 8) * q ** 7
                + q ** 10 + sign * sp.Rational(231, 128) * q ** 13)
        residual = root ** 2 - q ** 2 * (1 + root ** 3)
        assert_zero(truncate(residual, q, 17), f"Cubic small root with sign {sign}")
    return "Both displayed small roots satisfy z^2-q^2(1+z^3)=0 modulo q^17."


def check_cubic_preparation() -> str:
    t, z, u = sp.symbols("t z u")
    polynomial = z ** 2 - t * (1 + z ** 3)
    prepared = (z ** 2 - t ** 2 / u ** 2 * z - t / u) * (u - t * z)
    # The exact product difference is precisely the defining equation for u.
    assert_zero(prepared - polynomial - z ** 2 * (u + t ** 3 / u ** 2 - 1),
                "Exact cubic preparation identity")
    u_series = 1 - t ** 3 - 2 * t ** 6 - 7 * t ** 9 - 30 * t ** 12
    assert_zero(truncate(u_series - 1 + t ** 3 / u_series ** 2, t, 15),
                "Series for the cubic unit coefficient")
    assert_zero(truncate(polynomial.subs(z, u_series / t) * t ** 2, t, 15),
                "Infinite cubic root after clearing its leading pole")
    return "Exact preparation identity verified; u=1-t^3-2t^6-7t^9-30t^12 modulo t^15."


def check_split_residues() -> str:
    q = sp.Symbol("q")
    order = 18
    # q=sqrt(t). Individually these residues start with +/-1/(2q).
    residue_sum = (sp.exp(q) - sp.exp(-q)) / (2 * q)
    expected = sum(q ** (2 * n) / sp.factorial(2 * n + 1) for n in range(order // 2))
    assert_zero(truncate(residue_sum - expected, q, order),
                "Cancellation of split-pole residues")
    z = sp.Symbol("z")
    exponential = sum(z ** k / sp.factorial(k) for k in range(order))
    for n in range(order // 2):
        coefficient = sp.expand(exponential * z ** (-2 * n - 2)).coeff(z, -1)
        assert_zero(coefficient - 1 / sp.factorial(2 * n + 1),
                    f"Coefficientwise contour residue at order t^{n}")
    return "Split-pole and coefficientwise residue formulas agree through t^8."


def check_ramified_residue() -> str:
    x = sp.Symbol("x")
    # phi has ramification index 3. Test every Laurent monomial in a fixed range.
    phi = x ** 3 * (1 + 2 * x + x ** 2)
    for n in range(-4, 5):
        residue = sp.residue(phi ** n * sp.diff(phi, x), x, 0)
        assert_zero(residue - (3 if n == -1 else 0),
                    f"Residue substitution for monomial X^{n}")
    return "Residue substitution Res F(phi)phi'=3 Res F checked for powers -4 through 4."


def main() -> int:
    checks: list[tuple[str, Callable[[], str]]] = [
        ("Catalan inverse", check_catalan_inverse),
        ("Factorial ODE", check_factorial_ode),
        ("Cubic root clusters", check_cubic_roots),
        ("Cubic preparation", check_cubic_preparation),
        ("Split-pole residues", check_split_residues),
        ("Ramified residue transformation", check_ramified_residue),
    ]
    print("Surcomplex analysis: exact finite verification")
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    print("All arithmetic is exact. These checks are not proof-assistant certification.\n")
    for title, function in checks:
        try:
            detail = function()
        except Exception as exc:
            print(f"FAIL: {title}\n  {type(exc).__name__}: {exc}")
            return 1
        print(f"PASS: {title}\n  {detail}")
    print(f"\nAll {len(checks)} check groups passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
