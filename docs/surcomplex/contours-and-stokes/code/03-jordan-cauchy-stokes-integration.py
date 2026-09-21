#!/usr/bin/env python3
"""Exact checks accompanying the surcomplex contour article.

Requires Python 3.10+ and SymPy. No floating-point arithmetic, external services,
or general-purpose Hahn-field implementation is used. These finite checks do not
formally verify the general proofs in the article.

Usage: python verify_examples.py [--report verification.txt]
"""
from __future__ import annotations

import argparse
import itertools
import platform
from collections import Counter
from pathlib import Path
from typing import Sequence

import sympy as sp

COUNTS: Counter[str] = Counter()


def check(group: str, lhs: sp.Expr, rhs: sp.Expr, label: str) -> None:
    """Require an exact symbolic identity; raise on any nonzero remainder."""
    remainder = sp.cancel(sp.expand(lhs - rhs))
    if remainder != 0:
        remainder = sp.simplify(remainder)
    if remainder != 0:
        raise AssertionError(f"{group}: {label}: remainder {remainder}")
    COUNTS[group] += 1


def simplex_integral(expr: sp.Expr, variables: Sequence[sp.Symbol]) -> sp.Expr:
    """Integrate a polynomial over the positively oriented standard simplex."""
    polynomial = sp.Poly(sp.expand(expr), *variables)
    dim = len(variables)
    return sp.expand(sum(
        coefficient * sp.prod(sp.factorial(k) for k in powers)
        / sp.factorial(sum(powers) + dim)
        for powers, coefficient in polynomial.terms()
    ))


def monomials(variables: Sequence[sp.Symbol], degree: int):
    for powers in itertools.product(range(degree + 1), repeat=len(variables)):
        if sum(powers) <= degree:
            yield sp.prod(v**p for v, p in zip(variables, powers))


def triangle_checks() -> None:
    x, y, s = sp.symbols("x y s")
    edges = [(s, sp.S.Zero), (1 - s, s), (sp.S.Zero, 1 - s)]
    for monomial in monomials((x, y), 6):
        for component in range(2):
            P, Q = (monomial, sp.S.Zero) if component == 0 else (sp.S.Zero, monomial)
            boundary = 0
            for X, Y in edges:
                substitution = {x: X, y: Y}
                pulled = P.subs(substitution, simultaneous=True) * sp.diff(X, s)
                pulled += Q.subs(substitution, simultaneous=True) * sp.diff(Y, s)
                boundary += simplex_integral(pulled, (s,))
            interior = simplex_integral(sp.diff(Q, x) - sp.diff(P, y), (x, y))
            check("Triangle Stokes, degree <= 6", boundary, interior, f"{component}:{monomial}")


def tetrahedron_checks() -> None:
    x, y, z, u, v = sp.symbols("x y z u v")
    vertices = [sp.Matrix(p) for p in [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]]
    # A dy^dz + B dz^dx + C dx^dy, using the outward induced orientation.
    for monomial in monomials((x, y, z), 3):
        for component in range(3):
            coefficients = [sp.S.Zero] * 3
            coefficients[component] = monomial
            boundary = 0
            for omitted in range(4):
                face = [point for j, point in enumerate(vertices) if j != omitted]
                e, f = face[1] - face[0], face[2] - face[0]
                point = face[0] + u * e + v * f
                normal = e.cross(f)
                subs = dict(zip((x, y, z), point))
                pulled = sum(coefficients[j].subs(subs, simultaneous=True) * normal[j]
                             for j in range(3))
                boundary += (-1)**omitted * simplex_integral(pulled, (u, v))
            interior = simplex_integral(sum(sp.diff(coefficients[j], var)
                                             for j, var in enumerate((x, y, z))), (x, y, z))
            check("Tetrahedron Stokes, degree <= 3", boundary, interior,
                  f"{component}:{monomial}")


def geometric_examples() -> None:
    L, H, s = sp.symbols("L H s", real=True)
    paths = [L*s, L*(1-s) + sp.I*H*s, sp.I*H*(1-s)]
    integral = sum(simplex_integral(sp.conjugate(z)*sp.diff(z, s), (s,)) for z in paths)
    check("Geometric examples", integral, sp.I*L*H, "arbitrary aspect ratio triangle")
    W = sp.symbols("W", nonzero=True, real=True)
    check("Geometric examples", integral.subs({L: W, H: 1/W}), sp.I, "infinite-thin triangle")
    e, d, theta = sp.symbols("epsilon delta theta", real=True)
    z = (1+e)*sp.cos(theta) + sp.I*(1+d)*sp.sin(theta)
    pulled = sp.expand(sp.conjugate(z)*sp.diff(z, theta))
    ellipse = sp.integrate(pulled, (theta, 0, 2*sp.pi))
    check("Geometric examples", ellipse, 2*sp.pi*sp.I*(1+e)*(1+d), "deformed ellipse")


def root_of_unity_checks() -> None:
    X, q = sp.symbols("X q")
    # In Q(q)[X]/(X^n - 1), averaging over n-th roots extracts the constant
    # coefficient of the representative of degree < n. This is exact and
    # avoids numerical roots of unity.
    for n in range(1, 13):
        numerator = sum(q**j * X**j for j in range(n))
        check("Root-of-unity polynomial reduction", (1-q*X)*numerator,
              1-q**n*X**n, f"geometric product n={n}")
        reduced = sp.rem(sp.Poly(X*numerator, X), sp.Poly(X**n-1, X)).as_expr()
        average = sp.Poly(reduced, X).coeff_monomial(1)/(1-q**n)
        check("Root-of-unity polynomial reduction", average, q**(n-1)/(1-q**n),
              f"alias mean n={n}")
        check("Root-of-unity polynomial reduction", average.subs(q, sp.Rational(1, 2)),
              sp.Rational(2, 2**n-1), f"ordinary non-valuative convergence n={n}")


def residue_checks() -> None:
    z, t, rho, w = sp.symbols("z t rho w", nonzero=True)
    Q = 1/(z*z-t*t)
    plus, minus = 1/(2*t), -1/(2*t)
    check("Pole-cluster residues", Q, plus/(z-t)+minus/(z+t), "partial fractions")
    check("Pole-cluster residues", plus+minus, 0, "coarse residue cancellation")
    check("Pole-cluster residues", z*Q, sp.Rational(1, 2)/(z-t)+sp.Rational(1, 2)/(z+t),
          "numerator z")
    pulled = rho*Q.subs(z, t+rho*w)
    check("Pole-cluster residues", pulled, 1/(w*(2*t+rho*w)), "microscopic rescaling")
    check("Pole-cluster residues", sp.limit(w*pulled, w, 0), 1/(2*t), "small circle residue")
    truncated = sum(sp.Integer(j)**k*t**(j+2*k)*w**(k-1)
                    for j in range(1, 7) for k in range(7))
    residue = sp.expand(w*truncated).subs(w, 0)
    check("Radius-free circle coefficients", residue, sum(t**j for j in range(1, 7)),
          "truncated residue")
    for j in range(1, 7):
        check("Radius-free circle coefficients", sp.expand(residue).coeff(t, j), 1,
              f"coefficient t^{j}")


def two_variable_residues() -> None:
    # Companion example F1=x^2-A*y, F2=y^2-B*x. Compare the geometric-denominator
    # residue expansion against its finite quotient algebra on (1,x,y,xy).
    A, B = sp.symbols("A B")
    q = A*B
    Mx = sp.Matrix([[0,0,0,0], [1,0,0,q], [0,A,0,0], [0,0,1,0]])
    My = sp.Matrix([[0,0,0,0], [0,0,B,0], [1,0,0,q], [0,1,0,0]])
    identity, zero = sp.eye(4), sp.zeros(4)
    for label, matrix in [("commutation", Mx*My-My*Mx),
                          ("first defining relation", Mx**2-A*My),
                          ("second defining relation", My**2-B*Mx)]:
        if matrix.applyfunc(sp.expand) != zero:
            raise AssertionError(f"Two-variable residue: {label}")
        COUNTS["Two-variable residue comparison"] += 1
    e0 = sp.Matrix([1,0,0,0])
    for p in range(6):
        for r in range(6):
            # Numerator x^p y^r times (-A*y)^k (-B*x)^ell.
            extracted = sum(A**k*B**ell for k in range(6) for ell in range(6)
                            if p+ell == 2*k+1 and r+k == 2*ell+1)
            normal_form_residue = (Mx**p * My**r * e0)[3]
            check("Two-variable residue comparison", normal_form_residue, sp.sympify(extracted),
                  f"x^{p} y^{r}")
            # Tr(M_H) = Res(H*(4xy-AB)) on this quotient.
            Hmatrix = Mx**p * My**r
            jacobian = 4*Mx*My-q*identity
            check("Two-variable trace-Jacobian", sp.trace(Hmatrix),
                  (Hmatrix*jacobian*e0)[3], f"x^{p} y^{r}")


def endpoint_transport() -> None:
    z, s, t = sp.symbols("z s t")
    F = z**3+t*z+t**2
    gamma = s+sp.I*s*(1-s)
    eta = t*(s*s+1)+sp.I*t*t*s
    T = sum(sp.diff(F, z, n).subs(z, gamma)*eta**(n+1)/sp.factorial(n+1)
            for n in range(4))
    difference = F.subs(z, gamma+eta)*sp.diff(gamma+eta, s)
    difference -= F.subs(z, gamma)*sp.diff(gamma, s)
    check("Endpoint transport", sp.diff(T, s), difference, "differential identity")
    check("Endpoint transport", simplex_integral(difference, (s,)),
          T.subs(s, 1)-T.subs(s, 0), "integrated endpoint identity")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, help="write the exact-check report here")
    args = parser.parse_args()
    triangle_checks()
    tetrahedron_checks()
    geometric_examples()
    root_of_unity_checks()
    residue_checks()
    two_variable_residues()
    endpoint_transport()
    lines = ["EXACT VERIFICATION REPORT", "Surcomplex contours, Jordan separation, and Stokes theory",
             f"Python {platform.python_version()}; SymPy {sp.__version__}", ""]
    for label, count in COUNTS.items():
        lines.append(f"PASS  {count:3d}  {label}")
    lines.extend(["", f"TOTAL: {sum(COUNTS.values())} exact checks passed.",
                  "", "All checks use symbolic rational/algebraic identities, not numerical sampling.",
                  "The tetrahedron checks use the induced alternating face orientations.",
                  "The radius-free example is truncated to j<=6 and k<=6 with rho=t^2.",
                  "The two-variable example is also discussed in the supplied geometry manuscript.",
                  "", "LIMITATION: These checks validate finite identities and illustrative examples.",
                  "They do not implement arbitrary Hahn fields, certify all supports, prove the", 
                  "general theorems, or certify novelty."])
    report = "\n".join(lines)+"\n"
    print(report, end="")
    if args.report:
        args.report.write_text(report, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
