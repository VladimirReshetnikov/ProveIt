#!/usr/bin/env python3
"""Exact finite symbolic checks for the surcomplex-analysis article.

These computations validate displayed truncations, not the general theorems.
Symbols q and s are formal variables: no finite number is substituted for omega.
Requires Python 3.9+ and SymPy. Run: python verify_examples.py
"""
from __future__ import annotations

import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


def require_zero(expression: sp.Expr, label: str) -> None:
    """Raise a diagnostic error on a failed exact identity."""
    remainder = sp.simplify(sp.expand(expression))
    if remainder != 0:
        raise AssertionError(f"{label}: nonzero remainder {remainder}")
    print(f"PASS: {label}")


def require_order(expression: sp.Expr, variable: sp.Symbol,
                  order: int, label: str) -> None:
    """Check that all coefficients of degrees < order vanish at zero."""
    require_zero(sp.series(expression, variable, 0, order).removeO(), label)


def main() -> int:
    q, s, T, w = sp.symbols("q s T w")
    I = sp.I
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    print("Exact symbolic checks; O-terms denote formal truncation ideals.\n")

    # Section 10: Y^3 - Y - q = 0 at its three ordinary simple roots.
    y_zero = -q - q**3 - 3*q**5
    y_plus = 1 + q/2 - 3*q**2/8 + q**3/2
    y_minus = -1 + q/2 + 3*q**2/8 + q**3/2
    require_order(y_zero**3-y_zero-q, q, 7, "cubic central root through q^5")
    require_order(y_plus**3-y_plus-q, q, 4, "cubic positive root through q^3")
    require_order(y_minus**3-y_minus-q, q, 4, "cubic negative root through q^3")

    # Section 13.1: the displacement of a simple zero through q^2.
    A, B, g0, g1, h0 = sp.symbols("A B g0 g1 h0", nonzero=True)
    c1 = -g0/A
    c2 = g0*g1/A**2 - B*g0**2/(2*A**3) - h0/A
    displacement = c1*q + c2*q**2
    local_equation = A*displacement + B*displacement**2/2 + q*(g0+g1*displacement) + q**2*h0
    require_order(local_equation, q, 3, "simple-zero displacement through q^2")

    # Section 13.2: F(T)=T^2 + q exp(T), preparation through q^2.
    p1 = 1+T
    p2 = -sp.Rational(1,2)-sp.Rational(2,3)*T
    u1 = (sp.exp(T)-1-T)/T**2
    u2 = (-p1*u1-p2)/T**2
    polynomial = T**2 + q*p1 + q**2*p2
    unit = 1 + q*u1 + q**2*u2
    F = T**2 + q*sp.exp(T)
    require_order(polynomial*unit-F, q, 3, "Weierstrass factorization through q^2")
    for index, coefficient in [(1, u1), (2, u2)]:
        at_zero = sp.limit(coefficient, T, 0)
        if at_zero.is_finite is not True:
            raise AssertionError(f"u_{index} has a nonremovable singularity: {at_zero}")
        print(f"PASS: unit coefficient u_{index} is removable at zero; value {at_zero}")

    # Here q=s^2. The two branches are conjugate for real s.
    rho_plus = I*s - s**2/2 - 3*I*s**3/8 + s**4/3
    rho_minus = -I*s - s**2/2 + 3*I*s**3/8 + s**4/3
    for name, root in [("plus", rho_plus), ("minus", rho_minus)]:
        require_order(root**2+s**2*sp.exp(root), s, 6,
                      f"double-zero {name} root through s^4")
    require_order(rho_plus+rho_minus-(-s**2+sp.Rational(2,3)*s**4), s, 5,
                  "prepared root sum through s^4")
    require_order(rho_plus*rho_minus-(s**2-s**4/2), s, 5,
                  "prepared root product through s^4")

    # Coefficientwise contour moments equal residues of the q-expansion.
    log_derivative = sp.series(sp.diff(F,T)/F, q, 0, 3).removeO().expand()
    expected = [sp.Integer(2), -q+sp.Rational(2,3)*q**2, -2*q+2*q**2]
    for k, target in enumerate(expected):
        moment = sum(q**j*sp.residue(T**k*log_derivative.coeff(q,j), T, 0)
                     for j in range(3))
        require_zero(moment-target, f"contour moment s_{k} through q^2")

    # Section 9: a nontrivial normalized disk-profile automorphism.
    G = w-q*w**2+2*q**2*w**3-5*q**3*w**4+14*q**4*w**5
    require_order(G+q*G**2-w, q, 5, "quadratic deformation inverse through q^4")

    # Section 13.3: A(T)=sum n! T^n solves T^2 A'+(T-1)A+1=0.
    # Truncating at degree N leaves a possible defect at degree N+1 only.
    N = 24
    factorial_series = sum(sp.factorial(n)*T**n for n in range(N+1))
    defect = T**2*sp.diff(factorial_series,T)+(T-1)*factorial_series+1
    require_zero(sp.expand(defect)-sp.factorial(N+1)*T**(N+1),
                 f"factorial differential identity through degree {N}")

    print("\nAll checks passed. General support, topology, and class-size claims are proved in the article, not by this script.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
