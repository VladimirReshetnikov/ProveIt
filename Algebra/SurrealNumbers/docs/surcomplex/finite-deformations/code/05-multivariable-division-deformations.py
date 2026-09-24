#!/usr/bin/env python3
"""Exact finite consistency checks for the accompanying research article.

Requires Python 3 and SymPy. These checks verify the worked algebraic examples;
they are not a formal verification of the general Hahn-series theorems.
Run: python verify_examples.py
"""
from __future__ import annotations

import sys
try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install SymPy before running: python -m pip install sympy") from exc


def main() -> None:
    x, y, a, b, c, T = sp.symbols("x y a b c T")
    F1, F2 = x**2-y-a, y**2-b*x-c
    P = sp.expand(F2.subs(y, x**2-a))
    assert P == x**4-2*a*x**2-b*x+a**2-c
    M = sp.Matrix([[0,0,0,c-a**2], [1,0,0,b], [0,1,0,2*a], [0,0,1,0]])
    I = sp.eye(4)
    Y = M**2-a*I
    zero = sp.zeros(4)
    assert sp.simplify(M**2-Y-a*I) == zero
    assert sp.simplify(Y**2-b*M-c*I) == zero
    assert sp.expand(M.charpoly(T).as_expr()-P.subs(x,T)) == 0
    J = sp.det(sp.Matrix([[sp.diff(F1,x),sp.diff(F1,y)],
                         [sp.diff(F2,x),sp.diff(F2,y)]]))
    assert sp.expand(J.subs(y,x**2-a)-sp.diff(P,x)) == 0
    print("PASS: elimination, companion matrix, both equations, characteristic polynomial, Jacobian")

    def rem(poly: sp.Expr) -> sp.Expr:
        return sp.rem(sp.expand(poly), P, x)

    def residue(poly: sp.Expr) -> sp.Expr:
        return sp.expand(rem(poly)).coeff(x, 3)

    H = sp.Matrix(4,4,lambda i,j: residue(x**(i+j)))
    expected_H = sp.Matrix([[0,0,0,1],[0,0,1,0],[0,1,0,2*a],[1,0,2*a,b]])
    assert H == expected_H
    assert sp.expand(H.det()) == 1
    moments = [sp.expand(residue(x**k)) for k in range(17)]
    for k in range(13):
        assert sp.expand(moments[k+4]-2*a*moments[k+2]-b*moments[k+1]+(a**2-c)*moments[k]) == 0
        assert sp.expand(residue(x**k*sp.diff(P,x))-sp.trace(M**k)) == 0
    print("PASS: perfect residue Gram matrix, determinant 1, recurrence, 13 trace-Jacobian identities")
    for k in range(3, 11):
        print(f"  R(x^{k}) = {moments[k]}")

    # Check the all-order moment expression at thirteen finite degrees.
    for k in range(3,16):
        proposed = 0
        for r in range(k+1):
            for s in range(k+1):
                for u in range(k+1):
                    if 3+2*r+3*s+4*u == k:
                        multinomial = sp.factorial(r+s+u)/(sp.factorial(r)*sp.factorial(s)*sp.factorial(u))
                        proposed += multinomial*(2*a)**r*b**s*(c-a**2)**u
        assert sp.expand(proposed-moments[k]) == 0
    print("PASS: multinomial moment formula through degree 15")

    disc = sp.factor(sp.discriminant(P,x))
    JacM = 4*M*Y-b*I
    trace_gram = sp.Matrix(4,4,lambda i,j: sp.trace(M**(i+j)))
    assert sp.simplify(trace_gram-H*JacM) == zero
    assert sp.expand(trace_gram.det()-disc) == 0
    assert sp.expand(JacM.det()-disc) == 0
    print("PASS: trace Gram = residue Gram times Jacobian multiplication; discriminant identity")
    print(f"  discriminant = {sp.expand(disc)}")

    # Rank-three valuation: v(a)=1, v(b)=omega, v(c)=omega^2.
    # Tuples are compared in (omega^2, omega, 1) order.
    disc_terms = sp.Poly(disc, a,b,c).terms()
    val_terms = [((powers[2],powers[1],powers[0]),coeff,powers) for powers,coeff in disc_terms]
    leading = min(val_terms, key=lambda item:item[0])
    assert leading[1] == -256 and leading[2] == (3,2,0)
    print("PASS: high-rank leading discriminant is -256*a^3*b^2")

    # Independent coefficient extraction for the transcendental coupled system.
    # The coefficient of a^r b^s is the ordinary double residue
    # exp((s+1)x+(r+1)y)/(x^(2r+2)y^(2s+2)).
    coefficients = {}
    for r in range(5):
        for s in range(5):
            cx = sp.expand(sp.series(sp.exp((s+1)*x),x,0,2*r+2).removeO()).coeff(x,2*r+1)
            cy = sp.expand(sp.series(sp.exp((r+1)*y),y,0,2*s+2).removeO()).coeff(y,2*s+1)
            actual = sp.simplify(cx*cy)
            formula = sp.Rational((s+1)**(2*r+1)*(r+1)**(2*s+1),
                                  sp.factorial(2*r+1)*sp.factorial(2*s+1))
            assert actual == formula
            coefficients[(r,s)] = actual
    assert coefficients[(0,0)] == 1
    assert coefficients[(1,0)] == coefficients[(0,1)] == sp.Rational(1,3)
    assert coefficients[(2,0)] == coefficients[(0,2)] == sp.Rational(1,40)
    assert coefficients[(1,1)] == sp.Rational(16,9)
    print("PASS: 25 independently extracted coefficients for the transcendental double residue")
    print("  coefficients through total parameter degree 2:")
    print("  1 + (a+b)/3 + (a^2+b^2)/40 + 16*a*b/9")
    print(f"\nAll checks passed. Python {sys.version.split()[0]}; SymPy {sp.__version__}.")
    print("Scope: exact finite symbolic verification only; no claim of proof-assistant certification.")


if __name__ == "__main__":
    main()
