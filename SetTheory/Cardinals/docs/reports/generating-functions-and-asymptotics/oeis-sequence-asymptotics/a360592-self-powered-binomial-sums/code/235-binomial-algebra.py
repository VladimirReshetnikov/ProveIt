#!/usr/bin/env python3
"""Exact rational finite defect, scalar, marked-cumulant and density generators.

c remains a symbolic marking variable. In signed_density only, c denotes t*mu.
The finite calculations do not certify the analytic remainders in the article.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from functools import lru_cache
import argparse
import math
from fractions import Fraction
import sympy as S
from common import emit, integer, new_file_path, require

r, h, c, t, u = S.symbols('r h c t u')

@lru_cache(None)
def defect(j):
    integer(j, 1, 8, "defect order")
    power_sum = S.summation((r-2*h)**j-r**j, (h, 0, r-1))
    return S.expand((-1)**(j+1)*(r**(j+1)/S.Integer(2*j*(j+1))+power_sum/j))

@lru_cache(None)
def associated_stirling(d, k):
    """Partitions into k blocks, every block of size at least 2."""
    if d == 0 and k == 0:
        return S.Integer(1)
    if d < 0 or k < 0 or 2*k > d or k == 0:
        return S.Integer(0)
    return k*associated_stirling(d-1,k)+(d-1)*associated_stirling(d-2,k-1)

def centered_moment(d):
    return S.Add(*(associated_stirling(d,k)*c**k*t**(d-k)
                   for k in range(d//2+1)))

def truncate(poly, weight):
    return S.Add(*(v*t**i*u**j for (i,j),v in S.Poly(S.expand(poly),t,u).terms()
                   if 2*i+j <= weight))

def expansion(order):
    integer(order, 0, 4, "scalar order")
    # Weight(t)=2, weight(u)=1. Extra odd weighted degree ensures O(t^(K+1)).
    weight = 2*order+1
    V = S.Rational(3,4)*c*c
    for j in range(1,order+2):
        V += t**(2*j)*defect(j).subs(r,(c+u)/t)
    V = truncate(V,weight)
    require(V.subs({t:0,u:0}) == 0, "uncancelled scalar constant")
    E, term = S.Integer(1), S.Integer(1)
    for j in range(1,weight+1):
        term = truncate(term*V/j,weight)
        E += term
    result = S.Integer(0)
    for (i,j),v in S.Poly(S.expand(E),t,u).terms():
        result += v*t**i*centered_moment(j)
    result = S.Poly(S.expand(result),t)
    return [S.expand(result.coeff_monomial(t**j)) for j in range(order+1)]


A=S.Rational(3,4)
b=-S.Rational(1,4)

def scalar_log_coeffs(K):
    integer(K, 0, 4, "logarithm order")
    C=expansion(K)
    L=[S.Integer(0)]*(K+1)
    for j in range(1,K+1):
        L[j]=S.expand(C[j]-sum(i*L[i]*C[j-i] for i in range(1,j))/j)
    return L

def theta(poly,order=1):
    integer(order, 0, 8, "cumulant order")
    for _ in range(order):
        poly=S.expand(c*S.diff(poly,c))
    return poly

def weighted_truncate(poly,weight):
    return S.Add(*(co*t**i*u**j for (i,j),co in S.Poly(S.expand(poly),t,u).terms()
                   if 2*i+j<=weight))

def signed_density(K):
    """Here c is theta=t*mu, not the original fixed lambda*t.

    Returns P_K(t,u;theta) and its ordinary-Poisson expectation Z_K.
    P/Z approximates the exact density with weighted L1 error O(t^(K+1)).
    Use the parity-conditioned expectation for exactly normalized signed mass.
    """
    integer(K, 0, 4, "density order")
    V=-A*c*c+(2*A*c+b*t)*(c+u)
    for j in range(1,K+2):
        V+=t**(2*j)*defect(j).subs(r,(c+u)/t)
    W=2*K+1
    V=weighted_truncate(V,W)
    P=term=S.Integer(1)
    for j in range(1,W//2+1):
        term=weighted_truncate(term*V/j,W)
        P+=term
    P=S.expand(P)
    Z=0
    for (i,j),co in S.Poly(P,t,u).terms():
        Z+=co*t**i*sum(associated_stirling(j,k)*c**k*t**(j-k)
                       for k in range(j//2+1))
    return P,S.expand(Z)


def binomial_defect(j):
    integer(j, 1, 8, 'binomial defect order')
    nu = S.Symbol('nu')
    return S.expand(-S.summation(h**j, (h, 0, r-1))/j
                    + r*nu**j/j - nu**(j+1)/S.Integer(j+1))


def finite_weights(n):
    """Full integer marked weights from their defining binomial sum."""
    integer(n, 0, 200, 'finite n')
    return {n-2*k: (n-k)**k * math.comb(n-k, k) for k in range(n//2+1)}


def recurrent_weights(n):
    """Independent rational adjacent-weight recurrence, ending at w_n=1.

    If k=(n-r)/2 and m=(n+r)/2, w_(r+2)/w_r =
    k*(1+1/m)^k/((r+1)*(r+2)). All returned weights are exact integers.
    """
    integer(n, 0, 200, 'finite n')
    result = {n: 1}
    for rr in range(n-2, -1, -2):
        k = (n-rr)//2
        m = (n+rr)//2
        ratio = Fraction(k, (rr+1)*(rr+2)) * Fraction(m+1, m)**k
        weight = Fraction(result[rr+2], 1) / ratio
        require(weight.denominator == 1, 'nonintegral marked recurrence')
        result[rr] = weight.numerator
    return result


def coefficients(order=4):
    integer(order, 0, 4, 'order')
    C = expansion(order)
    L = scalar_log_coeffs(order)
    return {'symbol_convention': 't=n^(-1/2); c is free, physical c=sqrt(e/2)',
            'scalar': [str(x) for x in C], 'log_scalar': [str(x) for x in L],
            'defect': {str(j): str(defect(j)) for j in range(1, order+2)},
            'cumulants': {str(hh): {'constant': str(-A*2**hh*c*c),
                         'leading': 'c/t', 'positive_powers':
                         [str(theta(L[j], hh)) for j in range(1, order+1)]}
                         for hh in range(1, 5)},
            'density': {str(k): {'P': str(signed_density(k)[0]),
                                 'Z_ordinary': str(signed_density(k)[1])}
                        for k in range(min(order, 2)+1)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=4)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(coefficients(args.order), args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
