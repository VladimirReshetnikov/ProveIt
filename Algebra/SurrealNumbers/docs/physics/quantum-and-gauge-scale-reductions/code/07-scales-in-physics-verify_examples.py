#!/usr/bin/env python3
"""Exact finite checks for Surreal Scales in Quantum Theory and Gauge Models.

This script verifies polynomial and finite-series identities with SymPy. It does
not construct a Hahn field, prove a general theorem, or provide Lean verification.
Run with Python 3 and SymPy 1.14.0 (the version used for the accompanying record).
"""
from __future__ import annotations

import argparse
import platform
from pathlib import Path
from typing import Callable, Sequence

import sympy as sp

Quaternion = tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]
RECORD: list[str] = []


def qmul(q: Sequence[sp.Expr], p: Sequence[sp.Expr]) -> Quaternion:
    """Hamilton product in the ordered basis 1, i, j, k."""
    a, b, c, d = q
    e, f, g, h = p
    return tuple(map(sp.expand, (
        a*e - b*f - c*g - d*h,
        a*f + b*e + c*h - d*g,
        a*g - b*h + c*e + d*f,
        a*h + b*g - c*f + d*e,
    )))  # type: ignore[return-value]


def qconj(q: Sequence[sp.Expr]) -> Quaternion:
    a, b, c, d = q
    return a, -b, -c, -d


def qnorm(q: Sequence[sp.Expr]) -> sp.Expr:
    return sp.expand(sum(x*x for x in q))


def chi(q: Sequence[sp.Expr]) -> sp.Matrix:
    a, b, c, d = q
    return sp.Matrix([[a+sp.I*b, c+sp.I*d], [-c+sp.I*d, a-sp.I*b]])


def scalar_zero(x: sp.Expr) -> bool:
    return sp.simplify(sp.expand(x)) == 0


def check(name: str, difference: object) -> None:
    """Record an exact zero identity, raising an informative error on failure."""
    if isinstance(difference, sp.MatrixBase):
        entries = list(difference)
    elif isinstance(difference, (tuple, list)):
        entries = list(difference)
    else:
        entries = [sp.sympify(difference)]
    for i, value in enumerate(entries):
        if not scalar_zero(sp.sympify(value)):
            raise AssertionError(f"{name}, entry {i}: {sp.simplify(value)}")
    RECORD.append(f"PASS  {name}")


def coefficients(matrix: sp.Matrix, variable: sp.Symbol, degree: int) -> sp.Matrix:
    return matrix.applyfunc(lambda x: sp.expand(x).coeff(variable, degree))


def truncate(matrix: sp.Matrix, variable: sp.Symbol, degree: int) -> sp.Matrix:
    return matrix.applyfunc(
        lambda x: sum(sp.expand(x).coeff(variable, k)*variable**k
                      for k in range(degree+1)))


def quaternion_checks() -> None:
    a, b, c, d, e, f, g, h = sp.symbols('a b c d e f g h', real=True)
    q, p = (a, b, c, d), (e, f, g, h)
    check("quaternion complex representation preserves products",
          chi(qmul(q, p)) - chi(q)*chi(p))
    check("quaternion complex representation preserves adjoints",
          chi(qconj(q)) - chi(q).conjugate().T)
    check("quaternion norm representation", chi(q).conjugate().T*chi(q)
          - qnorm(q)*sp.eye(2))
    check("quaternion determinant equals norm", chi(q).det() - qnorm(q))
    check("quaternion norm is multiplicative", qnorm(qmul(q, p))-qnorm(q)*qnorm(p))
    check("quaternion conjugation reverses products",
          [x-y for x, y in zip(qconj(qmul(q, p)), qmul(qconj(p), qconj(q)))])
    check("complex trace is twice real quaternion trace", sp.trace(chi(q))-2*a)


def plaquette_checks() -> None:
    c, s, d, u = sp.symbols('c s d u', real=True)
    qa, qb = (c, s, 0, 0), (d, 0, u, 0)
    loop = qmul(qmul(qmul(qa, qb), qconj(qa)), qconj(qb))
    # Exact reduction modulo cos^2 + sin^2 = 1 for each edge rotation.
    ideal = sp.groebner([c*c+s*s-1, d*d+u*u-1], c, d, s, u)
    reduce: Callable[[sp.Expr], sp.Expr] = lambda x: ideal.reduce(sp.expand(x))[1]
    check("exact commutator Wilson weight 2 sin^2(x) sin^2(y)",
          reduce(1-loop[0]-2*s*s*u*u))
    check("commutator plaquette remains a unit quaternion", reduce(qnorm(loop)-1))
    x, y = sp.symbols('x y', real=True)
    substitutions = {c: 1-x*x/2+x**4/24, s: x-x**3/6,
                     d: 1-y*y/2+y**4/24, u: y-y**3/6}

    def homogeneous(expr: sp.Expr, degree: int) -> sp.Expr:
        poly = sp.Poly(sp.expand(expr), x, y)
        return sum(coef*x**powers[0]*y**powers[1]
                   for powers, coef in poly.terms() if sum(powers) == degree)

    expanded = [sp.expand(z).subs(substitutions, simultaneous=True) for z in loop]
    check("plaquette mixed imaginary initial term is 2xy k",
          [homogeneous(expanded[j], 2)-(2*x*y if j == 3 else 0)
           for j in range(1, 4)])
    check("plaquette leading real energy is 2x^2y^2",
          homogeneous(1-expanded[0], 4)-2*x*x*y*y)


def quantum_checks() -> None:
    p = sp.symbols('p', positive=True)  # State interpretation assumes 0 < p < 1.
    rho = sp.diag(1-p, p, 0)
    sigma = sp.diag(1-p, 0, p)
    projection = sp.diag(0, 1, 1)
    a, b = projection*rho*projection, projection*sigma*projection
    check("sharp postselection: both input traces are one",
          [sp.trace(rho)-1, sp.trace(sigma)-1])
    check("sharp postselection: both branch weights equal p",
          [sp.trace(a)-p, sp.trace(b)-p])
    check("sharp postselection: exact orthogonal conditional outputs",
          [*(a/p-sp.diag(0, 1, 0)), *(b/p-sp.diag(0, 0, 1))])
    check("sharp postselection: input difference has eigenvalues 0,p,-p",
          (rho-sigma).charpoly().as_expr()
          - ((rho-sigma).charpoly().gen**3-p**2*(rho-sigma).charpoly().gen))
    check("sharp postselection: success-weighted distance equality", p*1-p)

    eps, eta, z = sp.symbols('epsilon eta z', positive=True)
    vector = sp.Matrix([1, eps, eta])
    state = vector*vector.T/(1+eps**2+eta**2)
    raw = projection*state*projection
    weight = sp.trace(raw)
    check("rare pure branch: exact success probability",
          weight - (eps**2+eta**2)/(1+eps**2+eta**2))
    conditional = (raw/weight).applyfunc(sp.cancel)
    scaled = conditional.subs(eta, eps*z).applyfunc(sp.cancel)
    expected = sp.Matrix([[0, 0, 0], [0, 1, z], [0, z, z*z]])/(1+z*z)
    check("rare pure branch: cancellation of the leading common scale", scaled-expected)
    check("rare pure branch: initial state at eta/epsilon=0",
          scaled.subs(z, 0)-sp.diag(0, 1, 0))

    I, X, Z = sp.eye(2), sp.Matrix([[0, 1], [1, 0]]), sp.diag(1, -1)
    a0, a1 = sp.kronecker_product(Z, I), sp.kronecker_product(X, I)
    b0 = sp.kronecker_product(I, (Z+X)/sp.sqrt(2))
    b1 = sp.kronecker_product(I, (Z-X)/sp.sqrt(2))
    bell = a0*(b0+b1)+a1*(b0-b1)
    r0, r1 = a0-(b0+b1)/sp.sqrt(2), a1-(b0-b1)/sp.sqrt(2)
    check("Bell sum-of-squares identity for the Pauli realization",
          2*sp.sqrt(2)*sp.eye(4)-bell-(r0*r0+r1*r1)/sp.sqrt(2))
    phi = sp.Matrix([1, 0, 0, 1])/sp.sqrt(2)
    check("Bell bound attained at 2 sqrt(2)", (phi.T*bell*phi)[0]-2*sp.sqrt(2))


def scalar_and_three_level_checks() -> None:
    delta, lam, a, b = sp.symbols('delta lambda a b', real=True)
    h = sp.Matrix([[a, b/delta], [b/delta, 1/delta**2]])
    polynomial = delta**2*(h-lam*sp.eye(2)).det()
    expected = delta**2*lam**2-(1+a*delta**2)*lam+a-b**2
    check("critically scaled 2-level characteristic polynomial", polynomial-expected)
    k0 = a-b*b
    low_approx = k0-delta**2*b*b*k0
    residual = sp.expand(expected.subs(lam, low_approx))
    check("scalar effective correction has residual O(delta^4)",
          [residual.coeff(delta, j) for j in range(4)])

    eps, eta = sp.symbols('epsilon eta', real=True)
    h3 = sp.Matrix([[0, 0, eps], [0, eta, eps], [eps, eps, 1]])
    characteristic = sp.expand((lam*sp.eye(3)-h3).det())
    expected3 = lam**3-(1+eta)*lam**2+(eta-2*eps**2)*lam+eps**2*eta
    check("3-level characteristic polynomial", characteristic-expected3)
    check("3-level symmetric factorization at eta=0",
          characteristic.subs(eta, 0)-lam*(lam**2-lam-2*eps**2))
    low = (1-sp.sqrt(1+8*eps**2))/2
    check("3-level exact negative eigenvalue at eta=0",
          characteristic.subs({eta: 0, lam: low}))
    check("3-level ground energy through order epsilon^8",
          sp.series(low, eps, 0, 10).removeO()
          - (-2*eps**2+4*eps**4-16*eps**6+80*eps**8))
    effective = -sp.ones(2)
    symmetric = sp.Matrix([1, 1])/sp.sqrt(2)
    antisymmetric = sp.Matrix([1, -1])/sp.sqrt(2)
    check("3-level effective ground vector is symmetric", effective*symmetric+2*symmetric)
    check("3-level effective orthogonal eigenvalue is zero", effective*antisymmetric)


def matrix_riccati_checks() -> None:
    # Formal lambda counts powers of E = Delta^2. Independent u,v retain the
    # noncommuting diagonal-scale structure. No numerical eigensolver is used.
    lam, u, v = sp.symbols('lambda u v', real=True)
    A = sp.Matrix([[2, 1], [1, -1]])
    D = sp.Matrix([[3, 1], [1, 2]])
    B = sp.Matrix([[1, 2], [-1, 1]])
    E0 = sp.diag(u, v)
    Di = D.inv()
    if D*E0 == E0*D:
        raise AssertionError("Test data must not commute with the scale matrix")
    Y = [-Di*B.T]
    F = [A+B*Y[0]]
    for degree in range(1, 4):
        convolution = sp.zeros(2)
        for k in range(degree):
            convolution += Y[k]*F[degree-1-k]
        yn = (Di*E0*convolution).applyfunc(sp.expand)
        Y.append(yn)
        F.append((B*yn).applyfunc(sp.expand))
    y = sum((lam**j*Y[j] for j in range(4)), sp.zeros(2))
    f = A+B*y
    residual = B.T+D*y-lam*E0*y*f
    for j in range(4):
        check(f"matrix Riccati residual, coefficient degree {j}",
              coefficients(residual, lam, j))
    S = truncate(sp.eye(2)+y.T*lam*E0*y, lam, 3)
    metric_residual = f.T*S-S*f
    for j in range(4):
        check(f"graph generator is metric self-adjoint, degree {j}",
              coefficients(metric_residual, lam, j))
    T = S-sp.eye(2)
    sqrt_s = truncate(sp.eye(2)+T/2-T*T/8, lam, 2)
    inv_sqrt_s = truncate(sp.eye(2)-T/2+sp.Rational(3, 8)*T*T, lam, 2)
    effective = truncate(sqrt_s*truncate(f, lam, 2)*inv_sqrt_s, lam, 2)
    C0 = B*Di*E0*Di*B.T
    check("matrix effective leading coefficient", coefficients(effective, lam, 0)-F[0])
    check("matrix effective anticommutator correction",
          coefficients(effective, lam, 1)+(C0*F[0]+F[0]*C0)/2)
    check("matrix effective Hermiticity through second order", effective.T-effective)
    check("matrix first Riccati correction",
          Y[1]+Di*E0*Di*B.T*F[0])


def dimension_checks() -> None:
    m, n = sp.symbols('m n', integer=True, positive=True)
    dim = lambda k: 2*k*k-k
    check("quaternion composite dimension-gap identity",
          dim(m)*dim(n)-dim(m*n)-2*m*n*(m-1)*(n-1))
    check("two quaternionic 2-level systems require 36 versus 28 directions",
          [dim(2)**2-36, dim(4)-28, dim(2)**2-dim(4)-8])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=None,
                        help='Also save the exact-check record to this path.')
    args = parser.parse_args()
    for group in (quaternion_checks, plaquette_checks, quantum_checks,
                  scalar_and_three_level_checks, matrix_riccati_checks,
                  dimension_checks):
        group()
    lines = [
        'EXACT SYMBOLIC VERIFICATION',
        'Surreal Scales in Quantum Theory and Gauge Models',
        f'Python {platform.python_version()}; SymPy {sp.__version__}',
        '',
        *RECORD,
        '',
        f'{len(RECORD)} named exact checks passed.',
        'Scope: finite polynomial and finite-series identities only.',
        'Not a Hahn-field implementation, general theorem prover, or Lean build.',
    ]
    record = '\n'.join(lines)+'\n'
    print(record, end='')
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(record, encoding='utf-8')


if __name__ == '__main__':
    main()
