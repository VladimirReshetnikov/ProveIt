#!/usr/bin/env python3
"""Exact checks for selected formulas in surreal_three_space.tex.

Requires Python 3.10+ and SymPy. Run: python verify_identities.py
These are finite algebra/series checks, not a formal proof of the article,
a surreal arithmetic implementation, or a verification of analytic transfer.
"""
from __future__ import annotations

import sys
from collections.abc import Callable, Iterable
import sympy as sp


def assert_zero(expr: sp.Expr | sp.MatrixBase) -> None:
    """Check each entry using exact rational simplification."""
    items: Iterable[sp.Expr] = list(expr) if isinstance(expr, sp.MatrixBase) else [expr]
    for item in items:
        value = sp.simplify(sp.trigsimp(item))
        if value != 0:
            raise AssertionError(f"Nonzero residual: {value}")


def cross_matrix(v: sp.MatrixBase) -> sp.Matrix:
    x, y, z = v
    return sp.Matrix([[0, -z, y], [z, 0, -x], [-y, x, 0]])


def quaternion_mul(q: tuple[sp.Expr, sp.MatrixBase],
                   p: tuple[sp.Expr, sp.MatrixBase]) -> tuple[sp.Expr, sp.Matrix]:
    a, b = q
    c, d = p
    return sp.expand(a*c-b.dot(d)), (a*d+c*b+b.cross(d)).applyfunc(sp.expand)


def vector_identities() -> None:
    u = sp.Matrix(sp.symbols('u0:3'))
    v = sp.Matrix(sp.symbols('v0:3'))
    w = sp.Matrix(sp.symbols('w0:3'))
    assert_zero(u.cross(v).dot(u.cross(v)) - u.dot(u)*v.dot(v) + u.dot(v)**2)
    assert_zero(u.cross(v.cross(w)) - v*u.dot(w) + w*u.dot(v))
    assert_zero(cross_matrix(u)**2 - u*u.T + u.dot(u)*sp.eye(3))


def gram_determinant() -> None:
    u = sp.Matrix(sp.symbols('u0:3'))
    v = sp.Matrix(sp.symbols('v0:3'))
    w = sp.Matrix(sp.symbols('w0:3'))
    P = sp.Matrix.hstack(u, v, w)
    assert_zero((P.T*P).det()-P.det()**2)


def spherical_gram() -> None:
    x, y, z = sp.symbols('x y z')
    D = 1+2*x*y*z-x*x-y*y-z*z
    G = sp.Matrix([[1, z, y], [z, 1, x], [y, x, 1]])
    assert_zero(G.det()-D)
    assert_zero((x-y*z)**2+D-(1-y*y)*(1-z*z))
    M = 1+x+y+z
    assert_zero(M*M+D-2*(1+x)*(1+y)*(1+z))


def spherical_excess_polynomial() -> None:
    x, y, z, d = sp.symbols('x y z d')
    D = 1+2*x*y*z-x*x-y*y-z*z
    M = 1+x+y+z
    expr = (2*(x-y*z+sp.I*d)*(y-z*x+sp.I*d)*(z-x*y+sp.I*d)
            +(1-x)*(1-y)*(1-z)*(M+sp.I*d)**2)
    assert_zero(sp.rem(sp.expand(expr), d*d-D, d))


def holonomy_quaternion() -> None:
    # Coordinates u=e1, v=(c,s,0), w=(a,b,h). Constraints are unit lengths.
    c, s, a, b, h = sp.symbols('c s a b h')
    q_uv = (1+c, sp.Matrix([0, 0, s]))
    q_vw = (1+a*c+b*s, sp.Matrix([s*h, -c*h, c*b-s*a]))
    q_wu = (1+a, sp.Matrix([0, h, -b]))
    scalar, vector = quaternion_mul(q_wu, quaternion_mul(q_vw, q_uv))
    M = 1+c+a+a*c+b*s
    G = sp.groebner([h*h+a*a+b*b-1, s*s+c*c-1], h, b, a, s, c)
    residuals = [scalar-2*M, vector[0]-2*s*h, vector[1], vector[2]]
    for expr in residuals:
        assert_zero(G.reduce(sp.expand(expr))[1])


def cayley_rotation() -> None:
    t = sp.Matrix(sp.symbols('t0:3'))
    K = cross_matrix(t)
    Q = sp.eye(3)+2*(K+K*K)/(1+t.dot(t))
    assert_zero(Q.T*Q-sp.eye(3))
    assert_zero(Q.det()-1)


def minimal_rotation() -> None:
    c, s = sp.symbols('c s')
    u = sp.Matrix([1, 0, 0])
    v = sp.Matrix([c, s, 0])
    K = cross_matrix(u.cross(v))
    Q = sp.eye(3)+K+K*K/(1+c)
    for expr in list(Q*u-v)+list(Q.T*Q-sp.eye(3)):
        num = sp.together(expr).as_numer_denom()[0]
        assert_zero(sp.rem(sp.expand(num), s*s+c*c-1, s))


def gnomonic_metric() -> None:
    p, q = sp.symbols('p q', real=True)
    B = 1+p*p+q*q
    G = sp.Matrix([p, q, 1])/sp.sqrt(B)
    J = G.jacobian([p, q])
    expected = (B*sp.eye(2)-sp.Matrix([p, q])*sp.Matrix([[p, q]]))/B**2
    assert_zero(J.T*J-expected)
    assert_zero(expected.det()-1/B**3)
    assert_zero(G.dot(G)-1)


def stereographic_metric() -> None:
    p, q = sp.symbols('p q', real=True)
    B = 1+p*p+q*q
    H = sp.Matrix([2*p, 2*q, p*p+q*q-1])/B
    J = H.jacobian([p, q])
    assert_zero(H.dot(H)-1)
    assert_zero(J.T*J-4*sp.eye(2)/B**2)


def spherical_coordinate_metric() -> None:
    r, t, f = sp.symbols('r t f', real=True)
    X = r*sp.Matrix([sp.sin(t)*sp.cos(f), sp.sin(t)*sp.sin(f), sp.cos(t)])
    J = X.jacobian([r, t, f])
    assert_zero(J.T*J-sp.diag(1, r*r, r*r*sp.sin(t)**2))
    assert_zero(J.det()-r*r*sp.sin(t))


def ssa_candidates() -> None:
    P, Q, X, T = sp.symbols('P Q X T', real=True)
    L = P*P+Q*Q
    for sign in (1, -1):
        C = (X*P-sign*T*Q)/L
        S = (X*Q+sign*T*P)/L
        assert_zero(P*C+Q*S-X)
        num = sp.together(C*C+S*S-1).as_numer_denom()[0]
        assert_zero(sp.rem(sp.expand(num), T*T-(L-X*X), T))
    # Filtering S>0, L>0, and exceptional L=0 are separate proof obligations.


def skew_line_parameters() -> None:
    A, B, C, ru, rv = sp.symbols('A B C ru rv')
    L = A*C-B*B
    t = (C*ru-B*rv)/L
    s = (B*ru-A*rv)/L
    assert_zero(A*t-B*s-ru)
    assert_zero(B*t-C*s-rv)


def sphere_tangency_and_circumcenter() -> None:
    e = sp.symbols('e', positive=True)
    t = sp.sqrt(2*e-e*e)
    assert_zero(t*t+(1-e)**2-1)
    c = sp.Matrix([sp.Rational(1, 2), sp.Rational(1, 2), 1/e+e/2])
    vertices = [sp.zeros(3, 1), sp.Matrix([1, 0, 0]),
                sp.Matrix([0, 1, 0]), sp.Matrix([2, 0, e])]
    for vertex in vertices:
        assert_zero((c-vertex).dot(c-vertex)-c.dot(c))


def symmetric_small_triangle_area() -> None:
    h = sp.symbols('h', positive=True)
    E = 2*sp.atan(h*h/(sp.sqrt(1+h*h)+1)**2)
    expected = h*h/2-h**4/4+sp.Rational(7, 48)*h**6
    assert_zero(sp.series(E, h, 0, 8).removeO()-expected)


def hemispherical_branch() -> None:
    e = sp.symbols('e', positive=True)
    A = sp.sqrt(1+e*e)
    d = sp.sqrt(3)*e/(2*A)
    M = sp.Rational(1, 2)-1/A
    deficit = 2*sp.atan(d/(-M))
    assert_zero(sp.series(deficit, e, 0, 3).removeO()-2*sp.sqrt(3)*e)


def normal_coordinate_curvature() -> None:
    # Scale lengths by h; R=1. Compare degree-four cosine coefficients.
    h, r, s, k = sp.symbols('h r s k')
    # k is the cosine of the angle between the two tangent vectors.
    exact_cos = sp.cos(h*r)*sp.cos(h*s)+k*sp.sin(h*r)*sp.sin(h*s)
    L2 = r*r+s*s-2*k*r*s
    W = r*r*s*s*(1-k*k)
    distance_squared = h*h*L2-h**4*W/3
    cos_jet = 1-distance_squared/2+distance_squared**2/24
    assert_zero(sp.series(exact_cos-cos_jet, h, 0, 6).removeO())


def inverse_cosine_endpoint() -> None:
    h = sp.symbols('h', positive=True)
    # Verify the stated inverse asymptotic by composing with cosine.
    theta = sp.sqrt(2*h)*(1+h/12)
    assert_zero(sp.series(sp.cos(theta)-(1-h), h, 0, 3).removeO())


def gnomonic_area_factor() -> None:
    a, b, c, d, e, f = sp.symbols('a b c d e f')
    P = sp.Matrix([[a, c, e], [b, d, f], [1, 1, 1]])
    H = sp.Matrix([[c-a, e-a], [d-b, f-b]]).det()
    assert_zero(P.det()-H)


def tetrahedral_cayley_menger() -> None:
    # Generic tetrahedron 0,(a,0,0),(b,c,0),(d,e,f).
    a, b, c, d, e, f = sp.symbols('a b c d e f')
    v = [sp.zeros(3, 1), sp.Matrix([a, 0, 0]),
         sp.Matrix([b, c, 0]), sp.Matrix([d, e, f])]
    M = sp.ones(5)
    M[0, 0] = 0
    for i in range(4):
        for j in range(4):
            z = v[i]-v[j]
            M[i+1, j+1] = z.dot(z)
    assert_zero(M.det()-8*(a*c*f)**2)


def main() -> int:
    tests: list[tuple[str, Callable[[], None]]] = [
        ('Lagrange, vector triple product, and cross matrix', vector_identities),
        ('Generic three-vector Gram determinant', gram_determinant),
        ('Spherical Gram and half-excess denominator', spherical_gram),
        ('Spherical-excess polynomial modulo d^2=D', spherical_excess_polynomial),
        ('Quaternion holonomy numerator on unit constraints', holonomy_quaternion),
        ('Rational Cayley rotation orthogonality and determinant', cayley_rotation),
        ('Minimal rotation with unit-circle constraint', minimal_rotation),
        ('Gnomonic norm, metric, and area determinant', gnomonic_metric),
        ('Stereographic norm and conformal metric', stereographic_metric),
        ('Spherical-coordinate metric and Jacobian', spherical_coordinate_metric),
        ('SSA candidate line and circle equations', ssa_candidates),
        ('Closest-line parameter equations', skew_line_parameters),
        ('Sphere tangency and almost planar tetrahedron center', sphere_tangency_and_circumcenter),
        ('Small right-triangle excess through degree six', symmetric_small_triangle_area),
        ('Near-hemisphere excess branch and leading correction', hemispherical_branch),
        ('Normal-coordinate curvature correction', normal_coordinate_curvature),
        ('Inverse-cosine endpoint expansion by composition', inverse_cosine_endpoint),
        ('Gnomonic determinant area factor', gnomonic_area_factor),
        ('Cayley-Menger determinant for generic tetrahedron', tetrahedral_cayley_menger),
    ]
    print('Selected exact checks for Analytic Geometry and Trigonometry in Surreal Three-Space')
    print(f'Python {sys.version.split()[0]}; SymPy {sp.__version__}')
    failures = 0
    for index, (name, function) in enumerate(tests, 1):
        try:
            function()
        except Exception as exc:
            failures += 1
            print(f'{index:02d} FAIL: {name}: {type(exc).__name__}: {exc}')
        else:
            print(f'{index:02d} PASS: {name}')
    print(f'\n{len(tests)-failures}/{len(tests)} groups passed.')
    print('Scope: selected algebraic/series identities only; not a full formal verification.')
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
