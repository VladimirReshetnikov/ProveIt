"""Exact asymptotic jets and independent numerical evaluations.

All jets are ordinary Taylor coefficients, not derivatives.  The paper's
analytic proofs are separate from these finite tests and diagnostics.
Python 3.10+, SymPy and mpmath.  No network access is needed.
"""
from __future__ import annotations
from functools import lru_cache
from math import factorial
from typing import Sequence
import sympy as sp
import mpmath as mp


def mul(x: Sequence, y: Sequence, order: int) -> list:
    return [sum(x[j] * y[k-j] for j in range(max(0, k-len(y)+1), min(k+1, len(x))))
            for k in range(order+1)]


def exp_jet(logjet: Sequence, order: int) -> list:
    """exp(sum_{k>=1} logjet[k]*t**k), with constant coefficient one."""
    out = [1]
    for n in range(1, order+1):
        out.append(sum(k*logjet[k]*out[n-k] for k in range(1, n+1))/n)
    return out


@lru_cache(maxsize=256)
def coefficient_jets(a, b, c, u0, count: int, order: int) -> tuple:
    """A[j][q] = [t**q] A_j(u0+t;c), 0<=j<count, exact arithmetic.

    Pass SymPy Rational values or rational strings for exact computation.
    The Bernoulli convention is B_1(x)=x-1/2.
    """
    if count < 1 or order < 0:
        raise ValueError('count >= 1 and order >= 0 are required')
    a,b,c,u0 = map(sp.sympify, (a,b,c,u0))
    ell = [[sp.S.Zero]*(order+1)]
    for k in range(1, count):
        sign = sp.Rational((-1)**(k+1), k*(k+1))
        row = [sign*(sp.bernoulli(k+1,a-c)+sp.bernoulli(k+1,b-c)
                     -sp.bernoulli(k+1,1-c)-sp.bernoulli(k+1,a+b+u0-c))]
        for q in range(1, order+1):
            row.append(-sign*sp.binomial(k+1,q)*sp.bernoulli(k+1-q,a+b+u0-c)
                       if q <= k+1 else sp.S.Zero)
        ell.append([sp.expand(v) for v in row])
    out = [[sp.S.One]+[sp.S.Zero]*order]
    for j in range(1, count):
        row = [sp.S.Zero]*(order+1)
        for k in range(1, j+1):
            p = mul(ell[k],out[j-k],order)
            for q in range(order+1):
                row[q] += k*p[q]
        out.append([sp.expand(v/j) for v in row])
    return tuple(tuple(row) for row in out)


def as_mp(x):
    """Convert an exact real rational without an intermediate float."""
    x = sp.sympify(x)
    if x.is_Rational:
        return mp.mpf(str(x.p))/mp.mpf(str(x.q))
    return mp.mpf(str(x.evalf(mp.mp.dps+5)))


def residue(a, b, N: int):
    if N < 0:
        raise ValueError('N must be nonnegative')
    return sp.expand((-1)**N*sp.rf(1-sp.sympify(a),N)*sp.rf(1-sp.sympify(b),N)/sp.factorial(N))


def e_jet(a, b, N: int, order: int) -> list:
    """Taylor jet of E_N(t)=t*G(-N+t), including degenerate parameters."""
    a,b = as_mp(a),as_mp(b)
    logjet = [mp.mpf(0)]*(order+1)
    for k in range(1, order+1):
        g = -mp.euler if k == 1 else (-1)**k*mp.factorial(k-1)*mp.zeta(k)
        logjet[k] = (g-mp.polygamma(k-1,a)-mp.polygamma(k-1,b))/mp.factorial(k)
    out = exp_jet(logjet,order)
    for r in range(1,N+1):
        numerator = [(a-r)*(b-r),a+b-2*r,mp.mpf(1)]
        inverse = [-mp.mpf(1)/mp.mpf(r)**(k+1) for k in range(order+1)]
        out = mul(out,mul(numerator,inverse,order),order)
    return out


def term_jet(n: int, a, b, N: int, order: int) -> list:
    """Taylor coefficients of r_n(-N+t).  Reciprocal-Gamma zeros are retained."""
    aq,bq = sp.sympify(a),sp.sympify(b)
    d_exact = n+aq+bq-N
    aa,bb = as_mp(aq),as_mp(bq)
    prefactor = mp.gamma(n+aa)*mp.gamma(n+bb)/mp.factorial(n)
    if d_exact.is_Integer and d_exact <= 0:
        k = int(-d_exact)
        if order == 0:
            return [mp.mpf(0)]
        # 1/Gamma(-k+t) = (-1)^k k! t prod_{r=1}^k(1-t/r)/Gamma(1+t).
        logs = [mp.mpf(0)]*order
        if order > 1:
            logs[1] = mp.euler-mp.harmonic(k)
        for q in range(2,order):
            hk = mp.fsum(mp.mpf(1)/r**q for r in range(1,k+1))
            logs[q] = -(((-1)**q)*mp.zeta(q)+hk)/q
        ej = exp_jet(logs,order-1)
        fac = prefactor*((-1)**k)*mp.factorial(k)
        return [mp.mpf(0)]+[fac*x for x in ej]
    d = as_mp(d_exact)
    logs = [mp.mpf(0)]+[-mp.polygamma(k-1,d)/mp.factorial(k) for k in range(1,order+1)]
    return [prefactor*mp.rgamma(d)*v for v in exp_jet(logs,order)]


def zeta_jet(s, c, q: int):
    """Ordinary Taylor coefficient in the first (spectral) argument."""
    return mp.zeta(s,c,derivative=q)/mp.factorial(q)


def closed_jet(a,b,c,N: int,m: int,K: int|None=None):
    """Finite Stieltjes--Hurwitz formula for [t^m] R_K(-N+t)."""
    K = N+1 if K is None else K
    if K <= N:
        raise ValueError('K > N is required')
    aa = coefficient_jets(a,b,c,-N,K,m+1)
    aa = [[as_mp(v) for v in row] for row in aa]
    cc = as_mp(c)
    e = e_jet(a,b,N,m+1)
    value = e[m+1]-aa[N][m+1]
    value -= mp.fsum(aa[N][m-h]*((-1)**h)*mp.stieltjes(h,cc)/mp.factorial(h)
                      for h in range(m+1))
    for j in range(K):
        if j == N:
            continue
        value -= mp.fsum(aa[j][q]*zeta_jet(1-N+j,cc,m-q) for q in range(m+1))
    return value


def convergent_jet(a,b,c,N: int,m: int,M: int=80,J: int=24,K: int|None=None):
    """Independent series diagnostic: M actual terms plus an asymptotic tail.

    This is NOT a rigorous interval enclosure.  Repeat with larger M,J and
    precision.  No use is made of Gauss's closed formula or Stieltjes constants.
    """
    K = N+1 if K is None else K
    if not (N < K < J and M >= 1):
        raise ValueError('Require N < K < J and M >= 1')
    cc = as_mp(c)
    coeffs = [[as_mp(v) for v in row] for row in coefficient_jets(a,b,c,-N,J,m)]
    terms = []
    for n in range(M):
        x = n+cc
        logs = [(-mp.log(x))**q/mp.factorial(q) for q in range(m+1)]
        sub = mp.fsum(x**(N-1-j)*sum(coeffs[j][q]*logs[m-q] for q in range(m+1))
                     for j in range(K))
        terms.append(term_jet(n,a,b,N,m)[m]-sub)
    tail = mp.mpf(0)
    for j in range(K,J):
        tail += mp.fsum(coeffs[j][q]*zeta_jet(1-N+j,M+cc,m-q) for q in range(m+1))
    return mp.fsum(terms)+tail


def resonant_value(a,b,c,N: int):
    return as_mp(residue(a,b,N))*(mp.harmonic(N)-mp.euler-mp.digamma(as_mp(a))
                                 -mp.digamma(as_mp(b))+mp.digamma(as_mp(c)))

@lru_cache(maxsize=128)
def path_coefficient_jets(a,b,c,u0,alpha,beta,eta,count: int,order: int) -> tuple:
    """A_j along (a+alpha*t,b+beta*t,u0+eta*t), with fixed c."""
    a,b,c,u0,alpha,beta,eta = map(sp.sympify,(a,b,c,u0,alpha,beta,eta))
    ell = [[sp.S.Zero]*(order+1)]
    for k in range(1,count):
        sign=sp.Rational((-1)**(k+1),k*(k+1))
        row=[sign*(sp.bernoulli(k+1,a-c)+sp.bernoulli(k+1,b-c)
                   -sp.bernoulli(k+1,1-c)-sp.bernoulli(k+1,a+b+u0-c))]
        for q in range(1,order+1):
            if q>k+1:
                row.append(sp.S.Zero)
            else:
                row.append(sign*sp.binomial(k+1,q)*(
                    alpha**q*sp.bernoulli(k+1-q,a-c)
                    +beta**q*sp.bernoulli(k+1-q,b-c)
                    -(alpha+beta+eta)**q*sp.bernoulli(k+1-q,a+b+u0-c)))
        ell.append([sp.expand(v) for v in row])
    out=[[sp.S.One]+[sp.S.Zero]*order]
    for j in range(1,count):
        row=[sp.S.Zero]*(order+1)
        for k in range(1,j+1):
            prod=mul(ell[k],out[j-k],order)
            for q in range(order+1):
                row[q]+=k*prod[q]
        out.append([sp.expand(v/j) for v in row])
    return tuple(tuple(v) for v in out)


def tail_harmonic_sum(x,k: int,M: int=80,J: int=24):
    """Series + asymptotic tail diagnostic for the balanced harmonic-tail theorem."""
    if k<1:
        raise ValueError('k >= 1 is required')
    xx=as_mp(x)
    vals=[]
    for n in range(M):
        logs=[mp.mpf(0)]+[mp.zeta(2*j,n+xx)/j for j in range(1,k+1)]
        weight=mp.gamma(n+xx)**2/(mp.factorial(n)*mp.gamma(n+2*xx))
        vals.append(weight*exp_jet(logs,k)[k])
    a=path_coefficient_jets(x,x,1,0,1,-1,0,J,2*k)
    return mp.fsum(vals)+mp.fsum(as_mp(a[j][2*k])*mp.zeta(1+j,M+1) for j in range(1,J))
