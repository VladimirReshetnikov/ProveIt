#!/usr/bin/env python3
"""Exact identity checks for the tetrahedron, cube, and octahedron proofs.

Requires SymPy.  No numerical optimization or floating point is used.
This is an audit of displayed identities, not a substitute for the
geometric reduction or a claim of Lean/iPRA formal verification.
"""
import sympy as S


def zero(expression):
    assert S.cancel(S.expand(expression)) == 0, expression


def main():
    al, be, ga, de = S.symbols("alpha beta gamma delta")
    p = al + de - al * de - ga * de
    q = be + ga - be * ga - ga * de
    r = al * be - ga * de
    zero(p - (al * (1 - de) + de * (1 - ga)))
    zero(q - (be * (1 - ga) + ga * (1 - de)))
    zero((p - r) - (al * (1 - be) + de * (1 - al)))
    zero((q - r) - (be * (1 - al) + ga * (1 - be)))
    zero(1 - (p + q - r) - (al + ga - 1) * (be + de - 1))
    a, b, c, d = S.symbols("a b c d")
    sub = {al: a / (a + c), be: a / (a + d),
           ga: b / (b + d), de: b / (b + c)}
    zero((1 - (p + q - r)).subs(sub)
         - (a * b - c * d) ** 2 / ((a + c) * (a + d) * (b + c) * (b + d)))
    # Coefficients relative to the independent bivectors u∧v,u∧w,v∧w.
    v1 = S.Matrix([1-ga, -al, ga])
    v2 = S.Matrix([1-de, de, -be])
    cross = v1.cross(v2)
    zero(cross[2] - p)
    zero(cross[1] - q)  # cross y-coordinate is negative u∧w coefficient
    zero(cross[0] - r)
    print("Tetrahedron: six identities, height slack, and bivector formula verified.")

    r = S.symbols("r")
    zero(2 * (1+r)**4 - (2+r*r) * (1+2*r)**2 - r*r*(3+4*r-2*r*r))
    zero(3+4*r-2*r*r - (3+2*r+2*r*(1-r)))
    print("Cube: the exact hexagon slack identity verified.")

    D = (a+b)*(a+c)*(b+c)
    slack = D**2 - (a*a+b*b+c*c)*(a*b+a*c+b*c)**2
    positive = (2*(a**3*b**3+a**3*c**3+b**3*c**3)
                + 4*a*b*c*(a*a*b+a*a*c+a*b*b+a*c*c+b*b*c+b*c*c)
                + 7*a*a*b*b*c*c)
    zero(slack - positive)
    assert all(coefficient > 0 for coefficient in S.Poly(S.expand(slack),a,b,c).coeffs())
    P = S.Matrix([b,-a,0])/(a+b)
    Q = S.Matrix([c,0,-a])/(a+c)
    R = S.Matrix([0,c,-b])/(b+c)
    vector = P.cross(Q)+Q.cross(R)-R.cross(P)
    expected = 2*(a*b+a*c+b*c)/D*S.Matrix([a,b,c])
    for component in vector-expected:
        zero(component)
    print("Octahedron: area vector and positive ten-term certificate verified.")
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
