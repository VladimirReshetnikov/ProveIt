"""Universal closed coefficients of inverse-Gamma normal forms.

Uses positive polynomial coefficients and elementary beta moments, independently
of integration-by-parts reduction and the specialized four-variable formula.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, prod


def multiply(P, S):
    R={}
    for a,c in P.items():
        for b,d in S.items():R[a+b]=R.get(a+b,Q(0))+c*d
    return R


@lru_cache(None)
def central_polynomial(r: int):
    if r < 0: raise ValueError('r must be nonnegative')
    return {j:Q(1,2**r*factorial(j)*factorial(r+1-j))
            for j in range(r%2,r+1,2)}


@lru_cache(None)
def density(powers):
    """Product of C_r(v)^a_r, with two highest-index factors removed."""
    d=len(powers)-1;P={0:Q(1)}
    for r in range(1,d+1):
        for _ in range(powers[r]-(2 if r==d else 0)):
            P=multiply(P,central_polynomial(r))
    return P


def coefficient(powers):
    """Coefficient in N(A_m); m=sum((r+1)*a_r).

    powers is the finite tuple (a_0,...,a_d). Trailing zeros are allowed.
    """
    powers=tuple(powers)
    if any(not isinstance(a,int) or a<0 for a in powers):
        raise ValueError('all exponents must be nonnegative integers')
    while powers and powers[-1]==0:powers=powers[:-1]
    if len(powers)<=1:return Q(1)
    d=len(powers)-1
    if powers[-1]==1 or sum(r*a for r,a in enumerate(powers))%2:
        return Q(0)
    m=sum((r+1)*a for r,a in enumerate(powers))
    factor=Q((-1)**d*factorial(m),2**d*factorial(d+1)*prod(factorial(a) for a in powers))
    return factor*sum((c/Q(prod(e+1+2*j for j in range(d+1)))
                       for e,c in density(powers).items()),Q(0))
