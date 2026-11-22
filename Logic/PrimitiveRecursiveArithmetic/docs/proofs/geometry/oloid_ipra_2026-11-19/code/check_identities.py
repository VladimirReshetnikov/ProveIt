#!/usr/bin/env python3
"""Verify the oloid differential and elliptic certificates using exact algebra.

Run with Python 3 and SymPy. No numerical simplification or CAS integration is used.
The only integration in the script is the rational identity integral_0^1 t^j=1/(j+1).
"""
import sympy as sp

Q = sp.Rational
lam, q = sp.symbols("lam q")
cos_t = 2*q - 1
b = 1 + (2 - 3*lam)*cos_t


def polynomial_integral(expr, variable):
    polynomial = sp.Poly(expr, variable)
    return sum(coeff / (degree + 1) for (degree,), coeff in polynomial.terms())


def check_chart():
    # S=sin(theta), C=cos(theta), w=sqrt(q). The positive denominator w>=1/2.
    S, C, w = sp.symbols("S C w")
    q0 = w**2
    dqroot = -3*S*C / (4*w)

    def dtheta(expr):
        return C*sp.diff(expr, S) - S*sp.diff(expr, C) + dqroot*sp.diff(expr, w)

    def zero(expr):
        numerator = sp.fraction(sp.cancel(expr))[0]
        numerator = sp.rem(numerator, C**2 + S**2 - 1, C)
        numerator = sp.rem(numerator, w**2 + 3*S**2/4 - 1, w)
        return sp.expand(numerator) == 0

    A = sp.Matrix([Q(1, 2) - 2*q0, sp.sqrt(3)*S*w, 0])
    B = sp.Matrix([(1-q0)/(2*q0), 0, sp.sqrt(3)*C/(2*q0)])
    P = (1-lam)*A + lam*B
    n = sp.Matrix([1 - 2*q0, A[1], sp.sqrt(3)*C])
    cross = P.diff(lam).cross(P.applyfunc(dtheta))
    for i in range(3):
        assert zero(cross[i] - b.subs(q, q0)*n[i]/(2*w**3))
    assert zero(n.dot(n) - 4*w**2)
    assert zero(P.dot(n) - (q0 + Q(1, 2)))
    assert zero(A[0]*n[0] + A[1]*n[1] - B.dot(n))


def check_periods():
    # W/sqrt(q) is height times the Jacobian of the projection to the xy-plane.
    W = lam*(4*q - 1)*b/(4*q**2)
    x = (1-lam)*(Q(1, 2) - 2*q) + lam*(1-q)/(2*q)
    y2 = (1-lam)**2 * 4*q*(1-q)
    z2 = lam**2 * (4*q-1)/(4*q**2)
    u = 4*(1-q)/3

    def L(g):
        return ((1-2*u)*q - 3*u*(1-u)/4)*g - 3*u*(1-u)*q*sp.diff(g,q)/2

    assert sp.cancel(polynomial_integral(b/q, lam) - (1 + 1/(2*q))) == 0
    entries = [
        ("volume", 1, Q(2,3), Q(4,3), -(2*q-1)/(2*q**2)),
        ("axial inertia", y2 + z2/3, -Q(2,45), Q(32,45),
         -(128*q**4 + 16*q**3 + 4*q**2 - 18*q + 3)/(240*q**4)),
        ("transverse inertia", x**2 + z2/3, -Q(19,90), Q(71,45),
         (64*q**4 - 78*q**3 - 15*q**2 - 3*q + 3)/(120*q**4)),
    ]
    for name, column, k, e, g in entries:
        R = 4 * polynomial_integral(W*column, lam)
        assert sp.cancel(R - k - e*q - L(g)) == 0
        print(f"{name}: exact differential verified")


if __name__ == "__main__":
    check_chart()
    print("surface cross product, normal length and support height verified")
    check_periods()
