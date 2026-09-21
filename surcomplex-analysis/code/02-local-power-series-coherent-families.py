#!/usr/bin/env python3
"""Exact finite algebra checks for the accompanying Surcomplex Analysis article.

Requires Python 3.10+ and SymPy. Run: python verify_examples.py
The checks concern finite formal truncations. They do not certify the
normal-summability or class-theoretic arguments of the article.
"""
from __future__ import annotations

import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("This optional check script requires SymPy: pip install sympy") from exc


def require_equal(actual: sp.Expr, expected: sp.Expr, label: str) -> None:
    """Raise an informative error on failure, even with Python optimization enabled."""
    difference = sp.expand(actual - expected)
    if difference != 0:
        raise AssertionError(f"{label}: nonzero difference {difference}")


def truncate(expr: sp.Expr, variable: sp.Symbol, order: int) -> sp.Expr:
    """Return all terms of degree strictly smaller than order."""
    polynomial = sp.Poly(sp.expand(expr), variable)
    return sp.Add(*(coefficient * variable**monomial[0]
                    for monomial, coefficient in polynomial.terms()
                    if monomial[0] < order))


def check_preparation(order: int = 12) -> None:
    """Compute F=U W modulo t**(order+1), using Hermite division by Z**2."""
    z, t = sp.symbols("Z t")
    p: dict[int, sp.Expr] = {1: sp.Integer(-1)}
    q: dict[int, sp.Expr] = {1: z}
    for n in range(2, order + 1):
        cross = sp.expand(sum(q[j] * p[n-j] for j in range(1, n)))
        quotient, remainder = sp.div(cross, z**2, z)
        q[n], p[n] = -quotient, -remainder
        if p[n] != 0 and sp.degree(p[n], z) >= 2:
            raise AssertionError(f"Remainder degree condition failed at n={n}")
    w = z**2 + sum(p[n] * t**n for n in range(1, order + 1))
    unit = 1 + sum(q[n] * t**n for n in range(1, order + 1))
    target = z**2 - t + t*z**3
    require_equal(truncate(unit*w - target, t, order + 1), 0,
                  "Preparation product")
    for n, expected in {1: -1, 2: z, 4: -1, 5: 2*z, 7: -3}.items():
        require_equal(p[n], sp.sympify(expected), f"p_{n}")
    for n, expected in {1: z, 3: -1, 6: -2}.items():
        require_equal(q[n], sp.sympify(expected), f"q_{n}")
    print(f"PASS preparation recursion and product through t^{order}")
    print("  W =", sp.collect(sp.expand(w), z))
    print("  U =", sp.expand(unit))


def check_root_branches(order: int = 6) -> None:
    """Solve w**2*(1+q*w)=1 recursively near w=+1 and w=-1."""
    q, unknown = sp.symbols("q unknown")
    for sign in (1, -1):
        branch = sp.Integer(sign)
        coefficients: list[sp.Expr] = []
        for n in range(1, order + 1):
            candidate = branch + unknown*q**n
            equation = sp.expand(candidate**2*(1 + q*candidate) - 1).coeff(q, n)
            solutions = sp.solve(equation, unknown)
            if len(solutions) != 1:
                raise AssertionError(f"Expected a unique branch coefficient at n={n}")
            coefficient = solutions[0]
            branch += coefficient*q**n
            coefficients.append(coefficient)
        require_equal(truncate(branch**2*(1 + q*branch) - 1, q, order + 1),
                      0, f"Root branch {sign}")
        for actual, expected in zip(coefficients[:3],
                                     [-sp.Rational(1, 2), sign*sp.Rational(5, 8), -1]):
            require_equal(actual, sp.sympify(expected), "Displayed branch coefficient")
        print(f"PASS root branch with constant term {sign}: {branch}")
    print("  Substitute q=t^(3/2) and multiply the branch by t^(1/2).")


def check_lagrange(order: int = 9) -> None:
    y, alpha = sp.symbols("Y alpha")
    inverse = sum((-1)**(n-1) * sp.Rational(1, n)
                  * sp.binomial(2*n-2, n-1) * alpha**(n-1) * y**n
                  for n in range(1, order + 1))
    require_equal(truncate(inverse + alpha*inverse**2 - y, y, order + 1),
                  0, "Catalan inverse composition")
    print(f"PASS Lagrange/Catalan inverse through Y^{order}")


def main() -> int:
    check_preparation()
    check_root_branches()
    check_lagrange()
    print("All exact finite checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
