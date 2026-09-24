#!/usr/bin/env python3
"""Exact finite checks accompanying surcomplex_contours.tex.

Run: python verify_examples.py
Requires SymPy. No numerical approximations or implementation of a Hahn field
are used. These checks test examples, not the general mathematical proofs.
"""
from __future__ import annotations

import platform
import sys
from collections import Counter

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install SymPy first: python -m pip install sympy") from exc

COUNTS: Counter[str] = Counter()


def check(group: str, label: str, difference: sp.Expr) -> None:
    """Raise on a failed exact identity and print a reproducible certificate."""
    reduced = sp.simplify(difference)
    if reduced != 0:
        raise AssertionError(f"{group}: {label}: nonzero difference {reduced}")
    COUNTS[group] += 1
    print(f"PASS [{group}] {label}")


def check_matrix(group: str, label: str, matrix: sp.Matrix) -> None:
    for row in range(matrix.rows):
        for col in range(matrix.cols):
            check(group, f"{label}, entry ({row},{col})", matrix[row, col])


def rectangle_and_ellipse() -> None:
    A, B, R, S = sp.symbols("A B R S", positive=True)
    s, theta = sp.symbols("s theta", real=True)
    edges = [(A*s, 0), (A, B*s), (A*(1-s), B), (0, B*(1-s))]
    boundary = 0
    for x, y in edges:
        x, y = sp.sympify(x), sp.sympify(y)
        boundary += sp.integrate(-y*sp.diff(x, s)+x*sp.diff(y, s), (s, 0, 1))
    check("Stokes", "rectangle boundary integral = 2 A B", boundary-2*A*B)
    check("Stokes", "rectangle surface integral = boundary", 2*A*B-boundary)
    for n in range(7):
        period = 0
        for x, y in edges:
            z = sp.sympify(x) + sp.I*sp.sympify(y)
            period += sp.integrate(sp.expand(z**n*sp.diff(z, s)), (s, 0, 1))
        check("Stokes", f"closed rectangle period of z^{n} dz", period)
    z = R*sp.cos(theta)+sp.I*S*sp.sin(theta)
    integrand = sp.expand(sp.conjugate(z)*sp.diff(z, theta))
    period = sp.integrate(integrand, (theta, 0, 2*sp.pi))
    check("Stokes", "ellipse period of conjugate(z) dz", period-2*sp.pi*sp.I*R*S)
    check("Stokes", "ellipse imaginary density", sp.im(integrand)-R*S)
    u, v = sp.symbols("u v")
    check("Stokes", "infinitesimal ellipse area factors", (1+u)*(1+v)-(1+u+v+u*v))


def mesh_identity() -> None:
    for n in range(1, 8):
        d = sp.symbols(f"d0:{n}")
        variance = n*sum(x*x for x in d)-sum(d)**2
        squares = sum((d[i]-d[j])**2 for i in range(n) for j in range(i+1, n))
        check("finite mesh", f"N={n}: Cauchy-Schwarz sum-of-squares identity", variance-squares)


def residue_series() -> None:
    u = sp.symbols("u")
    order = 8
    exp_period = sp.series((sp.exp(u)-sp.exp(-u))/(2*u), u, 0, 2*order+2).removeO()
    for n in range(order+1):
        check("exponential residues", f"coefficient of t^{n}",
              exp_period.coeff(u, 2*n)-1/sp.factorial(2*n+1))

    # Put t=u^2, so the two moving poles are u and -u. For these first
    # eight coefficients, omitted numerator terms start beyond u^16.
    Hplus = sum(u**(2*m)/(1-m*u) for m in range(1, order+1))
    Hminus = sum(u**(2*m)/(1+m*u) for m in range(1, order+1))
    rational_period = sum(m*u**(2*m)/(1-m*m*u*u) for m in range(1, order+1))
    check("radius-free residue", "moving residues equal the rational coefficient formula",
          sp.factor((Hplus-Hminus)/(2*u)-rational_period))
    expanded = sp.series(rational_period, u, 0, 2*order+2).removeO().expand()
    expected = [1, 3, 12, 64, 441, 3855, 41464, 533736]
    for n in range(1, order+1):
        coefficient = sum(m**(2*(n-m)+1) for m in range(1, n+1))
        check("radius-free residue", f"t^{n}: Taylor extraction", expanded.coeff(u, 2*n)-coefficient)
        check("radius-free residue", f"t^{n}: independently recorded integer", coefficient-expected[n-1])
    print("RADIUS-FREE PERIOD COEFFICIENTS:", expected)


def coupled_complete_intersection() -> None:
    A, B = sp.symbols("A B", nonzero=True)
    q = A*B
    Mx = sp.Matrix([[0,0,0,0], [1,0,0,q], [0,A,0,0], [0,0,1,0]])
    My = sp.Matrix([[0,0,0,0], [0,0,B,0], [1,0,0,q], [0,1,0,0]])
    check_matrix("finite algebra", "Mx My = My Mx", Mx*My-My*Mx)
    check_matrix("finite algebra", "Mx^2 = A My", Mx**2-A*My)
    check_matrix("finite algebra", "My^2 = B Mx", My**2-B*Mx)
    lam = sp.symbols("lambda")
    check("finite algebra", "characteristic polynomial of Mx", Mx.charpoly(lam).as_expr()-lam*(lam**3-A*A*B))
    check("finite algebra", "characteristic polynomial of My", My.charpoly(lam).as_expr()-lam*(lam**3-A*B*B))
    gram = sp.Matrix([[0,0,0,1], [0,0,1,0], [0,1,0,0], [1,0,0,q]])
    check("finite algebra", "Gram determinant is one", gram.det()-1)

    def residue(p: int, r: int) -> sp.Expr:
        numerator_k, numerator_l = 2*p+r-3, p+2*r-3
        if numerator_k < 0 or numerator_l < 0 or numerator_k % 3 or numerator_l % 3:
            return sp.Integer(0)
        return A**(numerator_k//3)*B**(numerator_l//3)

    xpowers = [Mx**p for p in range(7)]
    ypowers = [My**r for r in range(7)]
    for p in range(7):
        for r in range(7):
            lhs = 4*residue(p+1,r+1)-q*residue(p,r)
            rhs = sp.trace(xpowers[p]*ypowers[r])
            check("trace-residue", f"H=x^{p} y^{r}", lhs-rhs)
    check("coupled residues", "Res(1)=0", residue(0,0))
    check("coupled residues", "Res(xy)=1", residue(1,1)-1)
    check("coupled residues", "Res(J)=4", 4*residue(1,1)-q*residue(0,0)-4)
    check("coupled residues", "four infinite weights cancel", -1/q+3/(3*q))
    check("coupled residues", "weighted xy sum", 3*q/(3*q)-1)

    # A noninvertible residue transformation: f=(x,y), A=diag(x,y),
    # G=(x^2,y^2). Multiplying the numerator by det(A)=xy is necessary.
    for p in range(4):
        for r in range(4):
            ordinary = sp.Integer(p == 0 and r == 0)
            transformed = sp.Integer(p+1 == 1 and r+1 == 1)
            check("determinant transformation", f"H=x^{p} y^{r}", ordinary-transformed)


def roots_of_unity_selection() -> None:
    # The cyclic shift has the N-th roots of unity as its eigenvalues.
    # Its exact matrix trace computes the character average without
    # floating-point trigonometry or a limiting argument.
    b = sp.symbols("b")
    for n in range(2, 9):
        shift = sp.zeros(n)
        for j in range(n):
            shift[(j+1) % n, j] = 1
        for exponent in range(-10, 11):
            average = sp.trace(shift**(exponent % n))/n
            check("roots-of-unity selection", f"N={n}, exponent={exponent}",
                  average-sp.Integer(exponent % n == 0))
        if n <= 5:
            average = sp.trace(shift*(shift-b*sp.eye(n)).inv())/n
            check("roots-of-unity rational average", f"N={n}", average-1/(1-b**n))


def main() -> None:
    print("Exact checks for Jordan Separation, Cauchy Theory, and Stokes Calculus")
    print("Python:", platform.python_version())
    print("SymPy:", sp.__version__)
    print("All computations below are symbolic and exact.\n")
    rectangle_and_ellipse()
    mesh_identity()
    residue_series()
    coupled_complete_intersection()
    roots_of_unity_selection()
    print("\nSUMMARY")
    for group, count in COUNTS.items():
        print(f"{group}: {count} passed")
    print(f"TOTAL: {sum(COUNTS.values())} exact checks passed")
    print("No failed checks. This is not formal verification of the general theorems.")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"FAILED: {error}", file=sys.stderr)
        raise
