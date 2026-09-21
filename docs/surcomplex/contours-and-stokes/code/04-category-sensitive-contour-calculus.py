#!/usr/bin/env python3
"""Exact checks for the examples in surcomplex_contours.tex.

Requires Python 3.10+ and SymPy.  No general Hahn-field implementation is used.
Run: python verify_examples.py
"""
from __future__ import annotations

import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

x, y, A, B, t, X = sp.symbols("x y A B t X")
checks = 0


def check(name: str, lhs: sp.Expr, rhs: sp.Expr) -> None:
    """Raise an informative error unless the symbolic identity holds exactly."""
    global checks
    difference = sp.cancel(sp.expand(lhs - rhs))
    if difference != 0:
        raise AssertionError(f"{name}: nonzero difference {difference}")
    checks += 1


def residue_original(p: int, q: int) -> sp.Expr:
    """Residue from the original complete-intersection perturbation expansion."""
    k_num, l_num = 2 * p + q - 3, p + 2 * q - 3
    if k_num < 0 or l_num < 0 or k_num % 3 or l_num % 3:
        return sp.Integer(0)
    return A ** (k_num // 3) * B ** (l_num // 3)


def residue_separated(polynomial: sp.Expr) -> sp.Expr:
    """Extract x^-1 y^-1 after division by Qx Qy on the separating torus."""
    total = sp.Integer(0)
    for (u, v), coeff in sp.Poly(polynomial, x, y).terms():
        if u >= 3 and v >= 3 and (u - 3) % 3 == 0 and (v - 3) % 3 == 0:
            k, l = (u - 3) // 3, (v - 3) // 3
            total += coeff * (A**2 * B) ** k * (A * B**2) ** l
    return sp.expand(total)


def main() -> int:
    F1, F2 = x**2 - A*y, y**2 - B*x
    Qx, Qy = x**4 - A**2*B*x, y**4 - A*B**2*y
    C = sp.Matrix([[x**2 + A*y, A**2], [B**2, y**2 + B*x]])
    D = x**2*y**2 + B*x**3 + A*y**3 + A*B*x*y - A**2*B**2
    J = 4*x*y - A*B
    transformed = C * sp.Matrix([F1, F2])
    check("first transformed denominator", transformed[0], Qx)
    check("second transformed denominator", transformed[1], Qy)
    check("transformation determinant", C.det(), D)
    check("Jacobian determinant", sp.det(sp.Matrix([[sp.diff(F1,x), sp.diff(F1,y)],
                                                   [sp.diff(F2,x), sp.diff(F2,y)]])), J)
    ideal = sp.groebner([F1, F2], x, y, domain=sp.QQ.frac_field(A, B))
    check("determinant quotient identity", ideal.reduce(sp.expand(D - A*B*J))[1], 0)

    for p in range(11):
        for q in range(11):
            check(f"residue x^{p} y^{q}", residue_separated(x**p*y**q*D),
                  residue_original(p, q))

    for label, H, expected in [
        ("one", sp.Integer(1), sp.Integer(0)),
        ("x", x, sp.Integer(0)),
        ("y", y, sp.Integer(0)),
        ("xy", x*y, sp.Integer(1)),
        ("Jacobian", J, sp.Integer(4)),
    ]:
        check(f"special residue {label}", residue_separated(H*D), expected)

    check("sum of four simple residue weights", -1/(A*B) + 3/(3*A*B), 0)
    check("xy weighted residue", 3*A*B/(3*A*B), 1)
    check("Jacobian weighted residue", (-A*B)/(-A*B) + 3*(3*A*B)/(3*A*B), 4)

    # Terms with n > 8 cannot contribute to the coefficient through degree eight.
    evaluated = sum(t**n/(1-n*t**2) for n in range(1, 9))
    truncated = sp.series(evaluated, t, 0, 9).removeO()
    expected_series = t + t**2 + 2*t**3 + 3*t**4 + 5*t**5 + 9*t**6 + 16*t**7 + 31*t**8
    check("radius-free evaluation through degree eight", truncated, expected_series)
    for m in range(1, 9):
        explicit = sum(sp.Integer(n)**k for n in range(1, m+1)
                       for k in range((m-n)//2+1) if n+2*k == m)
        check(f"radius-free coefficient {m}", truncated.coeff(t, m), explicit)

    # P'/P = sum_{zeta^N=1} 1/(X-zeta); hence mean zeta/(X-zeta)
    # equals X*P'/(N*P)-1, without approximation to the roots of unity.
    for degree in range(1, 13):
        P = X**degree - 1
        root_mean = X*sp.diff(P, X)/(degree*P) - 1
        check(f"root-sampling rational identity N={degree}", root_mean, 1/(X**degree - 1))
        check(f"root-sampling at two N={degree}", root_mean.subs(X, 2), sp.Rational(1, 2**degree - 1))

    print(f"PASS: {checks} exact symbolic checks.")
    print("121 monomial residues checked by two independent finite formulas.")
    print("Transformation matrix, determinant, Jacobian, and sample traces verified.")
    print("Radius-free Cauchy evaluation checked through exponent eight.")
    print("Roots-of-unity sampling identity checked symbolically for N=1,...,12.")
    print("These are example checks, not formal verification of the general theorems.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except AssertionError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
