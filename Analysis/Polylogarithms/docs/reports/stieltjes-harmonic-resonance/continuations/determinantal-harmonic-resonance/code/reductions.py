#!/usr/bin/env python3
"""Exact finite-cutoff and polylogarithmic reductions.

All arithmetic in this module is exact. L[p] means Li_p(z), and D[p]
means Li_{p,1}(z,1). These are symbols, not numerically evaluated objects.
"""
from __future__ import annotations
from functools import lru_cache
import sympy as sp

N, m, H, u, z = sp.symbols('N m H u z')

def L(p: int):
    return sp.Symbol(f'L{p}')

def D(p: int):
    return sp.Symbol(f'D{p}')

@lru_cache(None)
def moment(r: int, k: int):
    if r < 1 or not 0 <= k <= 2*r-2:
        raise ValueError('Require r>=1 and 0<=k<=2r-2.')
    d = 2*r-1
    residues = [sp.Rational((-j)**k * (-1)**(j-1),
                             sp.factorial(j-1)*sp.factorial(d-j))
                for j in range(1,d+1)]
    expected = sp.Integer(k==d-1)
    assert sum(residues)==expected
    rat = sum(c*(sum(1/(N+ell) for ell in range(2,j+1))
                   -sp.harmonic(j-1))
              for j,c in enumerate(residues,1))
    return sp.factor(rat)+expected*H

@lru_cache(None)
def cutoff(r: int):
    """Return A(N), B(N) such that cutoff sum = A H_(N+1)+B."""
    mat=sp.Matrix(r,r,lambda i,j:moment(r,i+j))
    A=sp.factor(mat[:r-1,:r-1].det(method='domain-ge')) if r>1 else sp.Integer(1)
    B=sp.factor(mat.subs(H,0).det(method='domain-ge'))
    return A,B

@lru_cache(None)
def maximum_mass(r: int):
    A,B=cutoff(r)
    expr=A*H+B-(A.subs(N,N-1)*(H-1/(N+1))+B.subs(N,N-1))
    return sp.cancel(expr.subs(N,m-1))

@lru_cache(None)
def rational_partition(r: int):
    C=sp.prod(sp.factorial(j)**3 for j in range(r))/sp.factorial(2*r-1)**r
    return sp.factor(C*sp.prod(sp.rf(u+r+k,r-k)/sp.rf(u+k,r) for k in range(r)))

def partial_fractions(expr, var=m):
    """Return a polynomial and triples (coefficient, integer shift, order)."""
    expr=sp.cancel(expr)
    num,den=sp.fraction(expr)
    poly,rem=sp.div(num,den,var)
    proper=sp.cancel(rem/den)
    factors=sp.factor_list(den,var)[1]
    terms=[]
    for fac, mult in factors:
        fp=sp.Poly(fac,var)
        if fp.degree()!=1:
            raise ValueError(f'Nonlinear denominator: {fac}')
        root=-fp.nth(0)/fp.nth(1)
        shift=-root
        if shift.is_integer is not True:
            raise ValueError('This implementation requires integral shifts.')
        germ=sp.cancel(proper*(var-root)**mult)
        for j in range(mult):
            c=sp.cancel(sp.diff(germ,var,j).subs(var,root)/sp.factorial(j))
            if c!=0:
                terms.append((c,int(shift),mult-j))
    rebuilt=poly+sum(c/(var+j)**p for c,j,p in terms)
    assert sp.cancel(rebuilt-expr)==0
    return poly,terms

def tail_rational(expr, start: int, var=m):
    """Sum z^k expr(k), k>=start, using ordinary polylog symbols."""
    poly, terms=partial_fractions(expr,var)
    if poly!=0:
        raise ValueError('Only proper rational tails used in this reducer.')
    out=0
    for c,j,p in terms:
        lo=start+j
        if lo<1:
            raise ValueError('A tail would cross a pole or nonpositive index.')
        out+=c*z**(-j)*(L(p)-sum(z**v/sp.Integer(v)**p for v in range(1,lo)))
    return sp.expand(out)

@lru_cache(None)
def harmonic_shift(p: int, j: int):
    """Sum z^m H_m/(m+j)^p for m>=1; p>=1,j>=0."""
    if p<1 or j<0:
        raise ValueError('Require p>=1,j>=0.')
    if j==0:
        return D(p)+L(p+1)
    out=D(p)-sum(z**k*sp.harmonic(k-1)/sp.Integer(k)**p for k in range(1,j+1))
    for ell in range(1,j):
        out-=tail_rational(1/(m**p*(m-ell)),j+1)
    return sp.expand(z**(-j)*out)

def transform_rational(expr, harmonic=False):
    """Generating sum for expr(m), or expr(m)H_m, m>=1."""
    poly,terms=partial_fractions(expr)
    if poly!=0:
        raise ValueError('The present exported examples use proper rational sequences.')
    out=0
    for c,j,p in terms:
        if j<0:
            raise ValueError('Nonpositive summation denominator.')
        out+=c*(harmonic_shift(p,j) if harmonic else
                 z**(-j)*(L(p)-sum(z**v/sp.Integer(v)**p for v in range(1,j+1))))
    return sp.expand(out)

@lru_cache(None)
def generating(r: int, primitive_order: int=0):
    if primitive_order<0:
        raise ValueError('primitive_order must be nonnegative.')
    expr=maximum_mass(r)/m**primitive_order
    A=sp.cancel(sp.diff(expr,H))
    B=sp.cancel(expr.subs(H,0))
    out=transform_rational(A,True)+transform_rational(B,False)
    return sp.collect(sp.expand(out),sorted(out.free_symbols-{z},key=str),func=sp.factor)

def euler_zeta(p: int):
    if p<2:
        raise ValueError('Convergent Euler height-one value requires p>=2.')
    return sp.Rational(p,2)*sp.zeta(p+1)-sp.Rational(1,2)*sum(
        sp.zeta(p-j)*sp.zeta(j+1) for j in range(1,p-1))

def endpoint(r: int,q: int):
    if q<1:
        raise ValueError('The unweighted endpoint diverges.')
    expr=sp.expand(generating(r,q))
    out=0
    for sym in sorted(expr.free_symbols-{z},key=str):
        coeff=sp.factor(expr.coeff(sym))
        at=sp.cancel(coeff).subs(z,1)
        name=str(sym); p=int(name[1:])
        if p==1:
            assert at==0, (r,q,sym,at)
        elif name[0]=='L':
            out+=at*sp.zeta(p)
        else:
            out+=at*euler_zeta(p)
    const=expr.subs({x:0 for x in expr.free_symbols-{z}})
    out+=const.subs(z,1)
    return sp.expand(out)

if __name__=='__main__':
    for r in range(1,5):
        A,B=cutoff(r)
        print(f'r={r}: cutoff A={A}, B={B}',flush=True)
        if r<=3:
            print('G=',generating(r),flush=True)
        for q in range(1,4):
            print(f'I({r},{q}) = {endpoint(r,q)}',flush=True)
