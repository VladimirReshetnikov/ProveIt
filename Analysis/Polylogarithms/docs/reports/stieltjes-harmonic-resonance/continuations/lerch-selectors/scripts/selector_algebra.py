"""Exact polynomial and endpoint routines for the accompanying article.

Conventions: H_n is the Frobenius--Euler polynomial, not a harmonic number.
F_j(s) = product(s-k, k=1,...,j+1).  No floating-point algebra is used.
"""
from __future__ import annotations
import sympy as sp

u, s, lam = sp.symbols('u s lam')

def frobenius_euler(degree: int, parameter: sp.Expr, variable: sp.Symbol = u) -> sp.Expr:
    if degree < 0 or int(degree) != degree:
        raise ValueError('degree must be a nonnegative integer')
    if parameter == 1:
        raise ValueError('the Frobenius--Euler basis is singular at parameter 1')
    h = [sp.Integer(1)]
    for n in range(1, degree + 1):
        h.append(sp.cancel(variable**n - sum(sp.binomial(n,k)*h[k] for k in range(n))/(1-parameter)))
    return sp.Poly(h[-1], variable).as_expr()

def falling_endpoint(j: int, variable: sp.Expr = s) -> sp.Expr:
    if j < 0:
        raise ValueError('j must be nonnegative')
    return sp.prod(variable-k for k in range(1,j+2))

def endpoint_spectrum(poly: sp.Expr, parameter: sp.Expr, length: sp.Expr = sp.Integer(1)) -> list[sp.Expr]:
    d = sp.degree(poly, u)
    if d is sp.S.NegativeInfinity:
        return []
    return [sp.cancel(sp.diff(poly,u,j).subs(u,length)-parameter*sp.diff(poly,u,j).subs(u,0)) for j in range(int(d)+1)]

def eulerian(n: int, variable: sp.Symbol = lam) -> sp.Expr:
    if n < 1:
        raise ValueError('the convention A_n begins at n=1')
    a=sp.Integer(1)
    for k in range(2,n+1):
        a=sp.expand((1+(k-1)*variable)*a+variable*(1-variable)*sp.diff(a,variable))
    return a

def negative_polylog(order: int, z: sp.Expr) -> sp.Expr:
    """Li_{-order}(z), order >= 0, by rational differentiation."""
    if order < 0:
        raise ValueError('order must be nonnegative')
    x=sp.Dummy('x'); a=x/(1-x)
    for _ in range(order):
        a=sp.cancel(x*sp.diff(a,x))
    return sp.cancel(a.subs(x,z))

def resonance_polynomial(degree: int, z: sp.Expr) -> sp.Expr:
    p=frobenius_euler(degree,z)
    return sp.expand(sum(sp.diff(p,u,j).subs(u,1)*sp.prod(s-k for k in range(j+2,degree+2)) for j in range(degree+1)))

def inverse_resonance_series(degree: int, m: int, order: int, epsilon: sp.Symbol) -> sp.Expr:
    if not 1<=m<=degree+1:
        raise ValueError('m must be one of 1,...,degree+1')
    coeff=[sp.Integer(1)]
    power_sums=[None]+[(-1)**r*sp.harmonic(m-1,r)+sp.harmonic(degree+1-m,r) for r in range(1,order+1)]
    for n in range(1,order+1):
        coeff.append(sp.expand(sum(power_sums[r]*coeff[n-r] for r in range(1,n+1))/n))
    return sum(coeff[n]*epsilon**n for n in range(order+1))
