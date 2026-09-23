#!/usr/bin/env python3
"""Exact finite checks accompanying 'Omnific Integers and Diophantine Geometry'.

Requires Python 3.9+ and SymPy. Run: python verify_examples.py
These checks do not formalize surreal numbers or arbitrary Hahn supports.
They verify only the finite identities and finite-support examples listed below.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, Mapping
import sys

try:
    import sympy as sp
except ImportError:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy")


def require_zero(name: str, value: object) -> None:
    """Fail loudly rather than treating an unevaluated expression as zero."""
    if isinstance(value, sp.MatrixBase):
        nonzero = [(i, j, sp.simplify(value[i, j]))
                   for i in range(value.rows) for j in range(value.cols)
                   if sp.simplify(value[i, j]) != 0]
        if nonzero:
            raise AssertionError(f"{name}: nonzero entries {nonzero}")
    else:
        reduced = sp.simplify(sp.expand(value))
        if reduced != 0:
            raise AssertionError(f"{name}: residual {reduced}")
    print(f"PASS  {name}")


Series = Dict[Fraction, sp.Expr]


def finite_product(a: Mapping[Fraction, sp.Expr],
                   b: Mapping[Fraction, sp.Expr]) -> Series:
    """Convolution for finite rational-exponent forms, with exact coefficients."""
    result: Series = {}
    for exponent_a, coefficient_a in a.items():
        for exponent_b, coefficient_b in b.items():
            exponent = exponent_a + exponent_b
            result[exponent] = result.get(exponent, sp.S.Zero) + coefficient_a * coefficient_b
    return {e: sp.simplify(c) for e, c in result.items() if sp.simplify(c) != 0}


def constant(form: Mapping[Fraction, sp.Expr]) -> sp.Expr:
    return form.get(Fraction(0), sp.S.Zero)


def check_finite_forms() -> None:
    forms: list[Series] = [
        {},
        {Fraction(0): sp.Integer(1)},
        {Fraction(0): sp.Integer(-3)},
        {Fraction(1): sp.Rational(1, 2)},
        {Fraction(1): sp.sqrt(2), Fraction(0): sp.Integer(7)},
        {Fraction(2): sp.Integer(-1), Fraction(1, 3): sp.sqrt(3),
         Fraction(0): sp.Integer(-5)},
        {Fraction(7, 2): sp.sqrt(2), Fraction(1, 2): -sp.sqrt(2),
         Fraction(0): sp.Integer(2)},
    ]
    checked = 0
    for a in forms:
        if any(e < 0 for e in a):
            raise AssertionError("Fixture contains a negative exponent")
        if constant(a).is_integer is not True:
            raise AssertionError("Fixture has a noninteger constant")
        for b in forms:
            product = finite_product(a, b)
            if sp.simplify(constant(product) - constant(a) * constant(b)) != 0:
                raise AssertionError("Constant coefficient product check failed")
            if a and b:
                top = max(a) + max(b)
                if max(product) != top:
                    raise AssertionError("Leading exponent check failed")
                if sp.simplify(product[top] - a[max(a)] * b[max(b)]) != 0:
                    raise AssertionError("Leading coefficient check failed")
            checked += 1
    print(f"PASS  {checked} finite-support products: constants and leading terms")


def main() -> None:
    print("Exact example checks for Omnific Integers and Diophantine Geometry")
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}\n")
    t, s, u, v, x, y, z, h = sp.symbols("t s u v x y z h")
    require_zero("Pythagorean polynomial identity",
                 (u*u-v*v)**2 + (2*u*v)**2 - (u*u+v*v)**2)
    norm = sp.resultant(h**3 - 2, x + y*h + z*h*h, h)
    target = x**3 + 2*y**3 + 4*z**3 - 6*x*y*z
    require_zero("Cubic norm via resultant", norm - target)
    multiplication = sp.Matrix([[x, 2*z, 2*y], [y, x, 2*z], [z, y, x]])
    require_zero("Cubic norm via multiplication determinant",
                 multiplication.det() - target)
    metric = sp.diag(1, -1, -1)
    nilpotent = sp.Matrix([[0, 0, 1], [0, 0, 1], [1, -1, 0]])
    identity = sp.eye(3)
    transform = identity + t*nilpotent + t*t*nilpotent**2/2
    require_zero("Nilpotence N^3 = 0", nilpotent**3)
    require_zero("Skewness N^t J + J N = 0",
                 nilpotent.T * metric + metric * nilpotent)
    require_zero("Lorentz preservation U(t)^t J U(t) = J",
                 transform.T * metric * transform - metric)
    require_zero("Lorentz determinant = 1", transform.det() - 1)
    require_zero("One-parameter group law",
                 transform.subs(t, s) * transform - transform.subs(t, s+t))
    require_zero("Lorentz inverse U(-t)", transform * transform.subs(t, -t) - identity)
    require_zero("Hyperboloid family with half coefficients",
                 (1+t*t/2)**2 - (t*t/2)**2 - t*t - 1)
    require_zero("Hyperboloid family with integral coefficients",
                 (1+2*t*t)**2 - (2*t*t)**2 - (2*t)**2 - 1)
    root_jet = sp.series(sp.sqrt(1+s), s, 0, 4).removeO()
    require_zero("First three nonconstant binomial coefficients",
                 root_jet - (1+s/2-s*s/8+s**3/16))
    require_zero("Euclidean remainder recurrence",
                 1 - 2*(sp.sqrt(2)-1) - (sp.sqrt(2)-1)**2)
    check_finite_forms()
    print("\nAll checks passed.")
    print("Scope: exact finite identities and listed finite-support cases only.")
    print("No Lean proof or arbitrary-transfinite-support verification is claimed.")


if __name__ == "__main__":
    main()
