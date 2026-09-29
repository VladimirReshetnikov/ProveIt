#!/usr/bin/env python3
"""Exact finite checks for Integer Pressure and a Missing Taylor Coefficient.

Requires Python 3.10+ and SymPy.  No floating-point tests are used here.
These checks supplement, and do not replace, the all-order proofs in article.tex.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any
import sympy as sp


def indices(m: int) -> list[int]:
    if not isinstance(m, int) or m < 1:
        raise ValueError('m must be a positive integer')
    return list(range(1-m, m))


def matrix(m: int, z: Any = 1) -> sp.Matrix:
    """Fourier matrix, with z = exp(2*pi*i*c)."""
    ix = indices(m)
    z = sp.sympify(z)
    if z == 0:
        raise ValueError('z must be nonzero')
    def entry(k: int, r: int) -> Any:
        j = 2*k-r
        if abs(j) > m:
            return sp.S.Zero
        return 2*sp.binomial(2*m, m+j)/sp.Integer(4)**m*z**(-j)
    return sp.Matrix([[entry(k, r) for r in ix] for k in ix])


def eulerian_row(n: int) -> list[int]:
    if n < 1:
        raise ValueError('n must be positive')
    row = [1]
    for k in range(2, n+1):
        row = [(j+1)*(row[j] if j < len(row) else 0)
               +(k-j)*(row[j-1] if j > 0 else 0) for j in range(k)]
    return row


def eigen_jet(m: int, order: int) -> tuple[list[Any], list[Any]]:
    """Taylor coefficients in t=pi*c (not derivatives), exact over Q(i)."""
    ix = indices(m)
    d = len(ix)
    a0 = matrix(m)
    v0 = sp.Matrix(eulerian_row(2*m-1))/sp.factorial(2*m-1)
    u = sp.ones(1, d)
    assert a0*v0 == v0 and (u*v0)[0] == 1
    bordered = (a0-sp.eye(d)).row_join(-v0).col_join(u.row_join(sp.zeros(1,1)))
    inverse = bordered.inv()
    mats = [a0]
    for n in range(1, order+1):
        mats.append(sp.Matrix(d,d,lambda a,b: a0[a,b]*(-2*sp.I*(2*ix[a]-ix[b]))**n/sp.factorial(n)))
    eigenvalues = [sp.S.One]
    vectors = [v0]
    pressure = [sp.S.Zero]
    for n in range(1, order+1):
        rhs = sp.zeros(d, 1)
        for k in range(1,n+1):
            rhs -= mats[k]*vectors[n-k]
        for k in range(1,n):
            rhs += eigenvalues[k]*vectors[n-k]
        sol = inverse*rhs.col_join(sp.zeros(1,1))
        vectors.append(sp.simplify(sol[:d, 0]))
        eigenvalues.append(sp.simplify(sol[d]))
        pressure.append(sp.simplify(eigenvalues[n]-sum(sp.Rational(k,n)*pressure[k]*eigenvalues[n-k] for k in range(1,n))))
    return eigenvalues, pressure


def direct_moment(m: int, n: int, sign: int) -> int:
    """Parseval on the exact polynomial prod_j (1+sign*x^(2^j))^m."""
    coeffs = [1]
    for j in range(n):
        stride = 2**j
        new = [0]*(len(coeffs)+m*stride)
        for k in range(m+1):
            fac = int(sp.binomial(m,k))*sign**k
            for r, value in enumerate(coeffs):
                new[r+k*stride] += fac*value
        coeffs = new
    return sum(value*value for value in coeffs)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-m', type=int, default=6,
                        help='largest order for exact Taylor checks (default: 6)')
    parser.add_argument('--output', type=Path, default=Path('verification.json'))
    args = parser.parse_args()
    if not 2 <= args.max_m <= 12:
        parser.error('--max-m must be between 2 and 12')
    lam, z, t = sp.symbols('lambda z t')
    result: dict[str, Any] = {'arithmetic': 'exact rational and Gaussian rational', 'tests': [], 'jets': {}}
    for m in range(1,11):
        a = matrix(m)
        expected = sp.prod(lam-sp.Rational(1,2)**j for j in range(2*m-1))
        assert sp.expand(a.charpoly(lam).as_expr()-expected) == 0
        row = sp.Matrix(eulerian_row(2*m-1))/sp.factorial(2*m-1)
        assert a*row == row
        assert a.det() == sp.Rational(1,2)**((m-1)*(2*m-1))
        result['tests'].append(f'm={m}: base spectrum, Eulerian eigenvector, determinant')
    for m in range(1,5):
        az = matrix(m,z)
        assert sp.simplify(az.det()-sp.Rational(1,2)**((m-1)*(2*m-1))) == 0
        assert sp.simplify(az.charpoly(lam).as_expr()-matrix(m,1/z).charpoly(lam).as_expr()) == 0
        result['tests'].append(f'm={m}: symbolic phase-independent determinant and reflection')
    for m in range(1,5):
        for sign in (1,-1):
            a = matrix(m,sign)
            v = sp.zeros(2*m-1,1); v[m-1]=1
            for n in range(7):
                computed = sp.Integer(2)**((2*m-1)*n)*v[m-1]
                assert computed == direct_moment(m,n,sign)
                v = a*v
        result['tests'].append(f'm={m}: exact polynomial moments, n=0..6, both signs')
    for m in range(2,args.max_m+1):
        order = 2*m+2
        rho,p = eigen_jet(m,order)
        fixed = sp.series(2*m*sp.log(sp.cos(t)),t,0,order+1).removeO()
        assert all(p[j] == 0 for j in range(1,order+1,2))
        assert all(sp.simplify(p[j]-fixed.coeff(t,j)) == 0 for j in range(1,2*m))
        assert p[2*m] == 0
        R = sp.simplify(2*(2**(2*m)-1)*sp.zeta(2*m)/sp.pi**(2*m))
        fixedrho = sp.series(sp.cos(t)**(2*m),t,0,order+1).removeO()
        assert sp.simplify(rho[2*m]-fixedrho.coeff(t,2*m)-R) == 0
        result['jets'][str(m)] = {'pressure_taylor_in_pi_c': {str(j): str(p[j]) for j in range(2,order+1,2)},
                                'escape_constant': str(R)}
        result['tests'].append(f'm={m}: exact jet through degree {order}; missing degree {2*m}')
    result['passed'] = True
    result['test_groups'] = len(result['tests'])
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
