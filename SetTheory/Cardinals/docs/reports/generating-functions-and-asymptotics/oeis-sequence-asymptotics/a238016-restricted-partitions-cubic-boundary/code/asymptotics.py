#!/usr/bin/env python3
"""Numerical forward and inverse asymptotic charts (not exact counts).

Use mpmath's mp.workdps or set mp.mp.dps before calling these functions.
The functions deliberately work in logarithms where possible.
"""
from __future__ import annotations
import json
from pathlib import Path
from functools import lru_cache
import mpmath as mp
import sympy as sp

@lru_cache(maxsize=1)
def _log_functions():
    c = sp.Symbol('c', positive=True)
    data = json.loads((Path(__file__).resolve().parent/'coefficients.json').read_text())
    return tuple(sp.lambdify(c,sp.sympify(v,locals={'c':c}),'mpmath') for v in data['log'])

def critical_log(x, c=1, order: int=5):
    """Log of the cubic profile p_x(c*x^3); x may be a positive real."""
    x, c = mp.mpf(x), mp.mpf(c)
    if x <= 0 or c <= 0 or not 0 <= order <= len(_log_functions()):
        raise ValueError('positive x,c and an available nonnegative order required')
    return (2*x+1/(4*c)+(x-3)*mp.log(x)+(x-1)*mp.log(c)-mp.log(2*mp.pi)
            +sum(_log_functions()[k-1](c)/x**k for k in range(1,order+1)))

def critical_inverse_chart(log_y, c=1):
    """Explicit two-correction Lambert-W inverse, accepting log(y)."""
    L, c = mp.mpf(log_y), mp.mpf(c)
    if L <= 0 or c <= 0:
        raise ValueError('log_y and c must be positive (large-y asymptotic chart)')
    w = mp.lambertw(c*mp.exp(2)*L)
    x0 = L/w
    D = 1/(4*c)-mp.log(2*mp.pi*c)
    d0 = (3*mp.log(x0)-D)/(w+1)
    d1 = (3*d0-d0*d0/2-_log_functions()[0](c))/(w+1)
    return x0+d0+d1/x0

def critical_inverse_newton(log_y, c=1, order: int=5):
    """Invert a specified truncated chart; not an integer inverse oracle."""
    L = mp.mpf(log_y)
    x0 = critical_inverse_chart(L,c)
    return mp.findroot(lambda x:critical_log(x,c,order)-L,(x0,x0+mp.mpf('0.01')))

def exponential_background(x,q=2):
    x,q = mp.mpf(x),mp.mpf(q)
    if x <= 0 or q <= 1:
        raise ValueError('x>0 and q>1 are required')
    return mp.log(q)*x*(x-1)-mp.loggamma(x+1)-mp.loggamma(x)

def exponential_inverse_chart(log_y,q=2):
    """Exact gamma-background inverse plus the first exponential sector."""
    L,q=mp.mpf(log_y),mp.mpf(q)
    if L <= 0 or q <= 1:
        raise ValueError('log_y>0 and q>1 are required')
    b=mp.log(q); s=mp.sqrt(L/b)
    d=mp.log(s)/b+(b-2)/(2*b)
    e=d*d/2+d/b+mp.log(2*mp.pi)/(2*b)
    guess=s+d+e/s
    X=mp.findroot(lambda x:exponential_background(x,q)-L,(guess,guess+1))
    derivative=b*(2*X-1)-mp.digamma(X+1)-mp.digamma(X)
    correction=X*(X*X-1)/4*mp.exp(-b*X)/derivative
    return X-correction

if __name__ == '__main__':
    mp.mp.dps=50
    print('Cubic chart recovered index:',critical_inverse_newton(critical_log(60)))
    print('Explicit cubic inverse:',critical_inverse_chart(critical_log(60)))
