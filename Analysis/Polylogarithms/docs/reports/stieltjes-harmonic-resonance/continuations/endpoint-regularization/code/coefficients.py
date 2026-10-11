#!/usr/bin/env python3
"""Finite exact coefficient calculus for endpoint regularization.

No arithmetic independence of the formal atoms is assumed. Symbols are used
only to check identities in a polynomial ring; analytic validity is proved
in the accompanying article. Python >=3.10, SymPy >=1.12.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import product
from math import factorial
import sympy as s

L = s.Symbol('L')
G = s.Symbol('G')  # Euler's constant, not the shifted gamma_0(a)

def g(r: int):
    return s.Symbol(f'g{r}')

def Z(k: int, r: int = 0):
    return s.Symbol(f'z{k}_{r}')  # spectral derivative of Hurwitz zeta at (k,a)

def z(k: int):
    return s.Symbol(f'z{k}')  # ordinary Riemann zeta value

def indices(bound: tuple[int, ...]) -> list[tuple[int, ...]]:
    if any(not isinstance(i, int) or i < 0 for i in bound):
        raise ValueError('A content bound must consist of nonnegative integers.')
    return sorted(product(*(range(i+1) for i in bound)), key=lambda a:(sum(a), a))

def sub(a, b):
    return tuple(x-y for x,y in zip(a,b))

def leq(a, b):
    return all(x<=y for x,y in zip(a,b))

def exp_coefficients(logcoef: dict, bound: tuple[int,...]) -> dict:
    """[u^alpha] exp(logcoef), using the total-degree Euler recurrence."""
    inds = indices(bound)
    zero = (0,)*len(bound)
    if logcoef.get(zero, 0) != 0:
        raise ValueError('Constant logarithmic coefficient must be zero.')
    out = {zero:s.Integer(1)}
    for a in inds[1:]:
        out[a] = s.expand(sum(sum(b)*v*out[sub(a,b)]
                             for b,v in logcoef.items()
                             if sum(b)>0 and leq(b,a))/sum(a))
    return out

def cumulants(bound: tuple[int,...], cutoff: bool = False) -> dict:
    out = {}
    for a in indices(bound)[1:]:
        k=sum(a); w=sum(r*m for r,m in enumerate(a))
        if k==1:
            r=next(r for r,m in enumerate(a) if m)
            v=g(r)
            if cutoff:
                v+=L**(r+1)/s.Integer(r+1)
        else:
            v=s.Rational((-1)**(k-1+w)*factorial(k-1),
                         s.prod(factorial(m) for m in a))*Z(k,w)
        out[a]=v
    return out

def cutoff_polynomials(bound: tuple[int,...]) -> dict:
    return exp_coefficients(cumulants(bound, cutoff=True), bound)

@lru_cache(None)
def gamma_moments(n: int) -> tuple:
    """Gamma^(j)(1), 0<=j<=n, in Q[G,zeta(2),...,zeta(n)]."""
    h=[s.Integer(1)]
    for j in range(1,n+1):
        h.append(s.expand(sum(((-G) if k==1 else (-1)**k*z(k))*h[j-k]
                              for k in range(1,j+1))/j))
    return tuple(s.expand(factorial(j)*h[j]) for j in range(n+1))

def abel_polynomial(P):
    degree=s.degree(P,L) if P != 0 else 0
    moments=gamma_moments(int(degree))
    return s.expand(sum(moments[j]*s.diff(P,L,j)/factorial(j)
                        for j in range(int(degree)+1)))

def endpoint_constants(bound: tuple[int,...]) -> dict:
    return {a:abel_polynomial(P).subs(L,0)
            for a,P in cutoff_polynomials(bound).items()}

def kernel_coefficient(a: tuple[int,...]):
    D=sum((r+1)*m for r,m in enumerate(a))
    den=s.prod(factorial(m)*(r+1)**m for r,m in enumerate(a))
    return gamma_moments(D)[D]/den

def specialize_a_one(expr):
    return s.expand(expr.subs({g(0):G, **{Z(k,0):z(k) for k in range(2,30)}}))

def finite_log_coefficients(rows: list[tuple], bound: tuple[int,...]) -> dict:
    """Logarithm of a finite product, independently using power sums."""
    out={}
    for a in indices(bound)[1:]:
        k=sum(a)
        v=sum(s.prod(row[r]**m for r,m in enumerate(a)) for row in rows)
        out[a]=s.Rational((-1)**(k-1)*factorial(k-1),
                           s.prod(factorial(m) for m in a))*v
    return out

def finite_direct(rows: list[tuple], bound: tuple[int,...]) -> dict:
    zero=(0,)*len(bound)
    out={a:s.Integer(0) for a in indices(bound)};out[zero]=s.Integer(1)
    for row in rows:
        new=out.copy()
        for a,v in out.items():
            for r,x in enumerate(row):
                b=list(a);b[r]+=1;b=tuple(b)
                if leq(b,bound):new[b]+=v*x
        out=new
    return out

def partitions(items: tuple):
    """Each set partition exactly once, as a tuple of tuples."""
    if not items:
        yield ()
        return
    x,*tail=items
    for p in partitions(tuple(tail)):
        yield ((x,),)+p
        for j in range(len(p)):
            yield p[:j]+((x,)+p[j],)+p[j+1:]

def mobius(p):
    return s.prod((-1)**(len(b)-1)*factorial(len(b)-1) for b in p)

if __name__=='__main__':
    for a in [(1,1),(2,1),(0,2)]:
        P=cutoff_polynomials(a)[a]
        print(a, 'cutoff =',P)
        print(a, 'Abel =',specialize_a_one(abel_polynomial(P)))
