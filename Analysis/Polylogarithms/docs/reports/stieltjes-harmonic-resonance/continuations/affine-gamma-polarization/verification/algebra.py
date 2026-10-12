"""Exact free differential-polynomial arithmetic, using rational coefficients.
Monomials are sorted tuples of derivative indices. No special-function
identities or numerical fitting are used by the normal-form algorithm.
"""
from fractions import Fraction as Q
from collections import Counter, defaultdict
from functools import lru_cache
from math import factorial


def clean(p):
    return {m: c for m, c in p.items() if c}


def add(p, q, scale=Q(1)):
    out = defaultdict(Q, p)
    for m, c in q.items():
        out[m] += scale*c
    return clean(out)


def derivative(p):
    out = defaultdict(Q)
    for m, c in p.items():
        for r, multiplicity in Counter(m).items():
            mm=list(m); mm.remove(r); mm.append(r+1)
            out[tuple(sorted(mm))] += multiplicity*c
    return clean(out)


@lru_cache(None)
def reduce_monomial(m):
    """Return (N,H) with m=N+D H in the functional-monomial normal form."""
    if not m or m[-1]==0 or m.count(m[-1])>=2:
        return {m:Q(1)}, {}
    r=m[-1]; a=m.count(r-1)
    t=tuple(sorted(m[:-1]+(r-1,)))
    H={t:Q(1,a+1)}
    remainder=add({m:Q(1)}, derivative(H), -1)
    N={}
    for mm,c in remainder.items():
        nn,hh=reduce_monomial(mm)
        N=add(N,nn,c); H=add(H,hh,c)
    return N,H


def normal_form(p):
    n={}; h={}
    for m,c in p.items():
        nn,hh=reduce_monomial(m)
        n=add(n,nn,c); h=add(h,hh,c)
    return n,h


def next_gamma(p):
    return add({(0,)+m:c for m,c in p.items()},derivative(p),-1)


def partitions(n, minimum=1):
    if n==0:
        yield ()
    for k in range(minimum,n+1):
        for rest in partitions(n-k,k):
            yield (k,)+rest


def bell_sector(a,k,r):
    """Construct only the factor-degree sector that can contribute to u0^a u1^k ur^2."""
    degree=a+k+2; derivsum=k+2*r; weight=degree+derivsum
    out={}
    for part in partitions(derivsum):
        if len(part)>degree:
            continue
        mon=(0,)*(degree-len(part))+part
        denom=1
        for j,mult in Counter(mon).items():
            denom *= factorial(mult)*factorial(j+1)**mult
        out[mon]=Q((-1)**derivsum*factorial(weight),denom)
    return out


def square_coefficient(a,k,r):
    if min(a,k)<0 or r<2:
        raise ValueError('Require a,k >= 0 and r >= 2.')
    if k%2:
        return Q(0)
    m=a+2*k+2*r+2
    den=factorial(a)*2**k*factorial(k)*2**(r+1)*factorial(r+1)
    for j in range(r+1):
        den *= k+2*j+1
    return Q((-1)**r*factorial(m),den)


def serial(p):
    return [{'indices':list(m),'coefficient':str(c)} for m,c in sorted(p.items())]
