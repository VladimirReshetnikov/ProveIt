#!/usr/bin/env python3
"""Numerical reference implementation for weighted-uniform high moments.

Arbitrary precision is provided by mpmath. Analytic infinite-tail bounds are
returned, but floating-point roundoff is NOT interval-certified. Exact rational
routines and symbolic tests provide separate checks of finite identities.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import comb, factorial
from typing import Sequence
import mpmath as mp


@dataclass
class TiltStats:
    log_laplace: mp.mpf
    cumulants: list[mp.mpf]  # index r; index 0 is unused
    head_terms: int = 0
    tail_terms: int = 0
    analytic_tail_bounds: list[mp.mpf] | None = None  # log L, kappa_1,...


def _validate(t: mp.mpf, q: mp.mpf) -> None:
    if not mp.isfinite(t) or t <= 0:
        raise ValueError("t must be finite and positive")
    if not mp.isfinite(q) or not 0 < q < 1:
        raise ValueError("q must lie strictly between 0 and 1")


def one_cumulant(y: mp.mpf, r: int) -> mp.mpf:
    """Cumulant of Exp(1) conditioned to [0,y]. Use y>=1/2 here."""
    if r < 1 or y <= 0:
        raise ValueError("r>=1 and y>0 are required")
    return mp.factorial(r-1) - y**r * mp.polylog(1-r, mp.exp(-y))


def geometric_stats(t: mp.mpf, q: mp.mpf, order: int = 6) -> TiltStats:
    """Infinite geometric product, with a Bernoulli-summed small-argument tail.

    Weights are (1-q)q^j, j>=0. The analytic tail error uses |B_2k|/(2k)! <=
    4/(2*pi)^(2k), so it bounds omitted series terms, not rounding errors.
    """
    t, q = mp.mpf(t), mp.mpf(q)
    _validate(t, q)
    if not 1 <= order <= 12:
        raise ValueError("order must be between 1 and 12")
    logq = mp.log(q)
    y = t * (1-q)
    ll = mp.mpf(0)
    cumulants = [mp.mpf(0) for _ in range(order+1)]
    count = 0
    while y >= mp.mpf("0.5"):
        ll += mp.log(-mp.expm1(-y)/y)
        for r in range(1, order+1):
            cumulants[r] += one_cumulant(y, r)
        y *= q
        count += 1
        if count > 250000:
            raise RuntimeError("head exceeds 250000 factors; use a mesh-accelerated method")
    ll -= y/(2*(1-q))
    cumulants[1] += y/(2*(1-q))
    ratio2 = (y/(2*mp.pi))**2
    tol = mp.power(10, -mp.mp.dps+12)
    bounds = [mp.inf]*(order+1)
    for k in range(1, 2000):
        m = 2*k
        power_sum = y**m / (-mp.expm1(m*logq))
        base = mp.bernoulli(m) * power_sum / m
        ll += base/mp.factorial(m)
        for r in range(1, min(m, order)+1):
            cumulants[r] += (-1)**r * base/mp.factorial(m-r)
        nextm = m+2
        denominator = -mp.expm1(nextm*logq)
        bounds[0] = 4 * ratio2**(k+1)/(nextm*denominator*(1-ratio2))
        for r in range(1, order+1):
            g = ratio2 * (mp.mpf(k+2)/(k+1))**(r-1)
            bounds[r] = (4*nextm**(r-1)*ratio2**(k+1)/(denominator*(1-g))
                         if g < 1 and nextm >= r else mp.inf)
        if nextm >= order and max(bounds) < tol:
            return TiltStats(ll, cumulants, count, k, bounds)
    raise RuntimeError("Bernoulli tail did not meet requested precision")


def finite_stats(t: mp.mpf, weights: Sequence[mp.mpf], order: int = 6) -> TiltStats:
    """Finite-array counterpart. Numerical differentiation handles tiny factors."""
    t = mp.mpf(t)
    a = [mp.mpf(x) for x in weights]
    if t <= 0 or not a or min(a) <= 0 or abs(mp.fsum(a)-1) > mp.mpf("1e-25"):
        raise ValueError("positive normalized weights and positive t are required")
    ll = mp.mpf(0)
    kappa = [mp.mpf(0)]*(order+1)
    for w in a:
        y = t*w
        ll += mp.log(-mp.expm1(-y)/y)
        if y >= mp.mpf("0.5"):
            for r in range(1, order+1):
                kappa[r] += one_cumulant(y, r)
        else:
            def cg(z):
                return mp.log(mp.expm1(-y*(1-z))/(-y*(1-z))) - mp.log(mp.expm1(-y)/(-y))
            for r in range(1, order+1):
                kappa[r] += mp.diff(cg, 0, r)
    return TiltStats(ll, kappa, len(a), 0)


def solve_saddle(n: int, stats_function) -> tuple[mp.mpf, TiltStats]:
    """Safeguarded Newton iteration for t-mu(t)=n on [n,2n]."""
    if not isinstance(n, int) or n < 1:
        raise ValueError("n must be a positive integer")
    lo, hi = mp.mpf(n), mp.mpf(2*n)
    t = (lo+hi)/2
    tolerance = mp.power(10, -mp.mp.dps+15)*n
    for _ in range(200):
        st = stats_function(t)
        mu, v = st.cumulants[1:3]
        residual = t-mu-n
        if abs(residual) <= tolerance:
            return t, st
        if residual > 0:
            hi = t
        else:
            lo = t
        derivative = 1-(mu-v)/t
        proposal = t-residual/derivative
        t = proposal if lo < proposal < hi else (lo+hi)/2
    raise RuntimeError("saddle iteration failed")


def first_correction(n: int, st: TiltStats) -> mp.mpf:
    """Delta=C_1/n in the article, in cancellation-resistant form."""
    v, k3, k4 = st.cumulants[2:5]
    d = n+v
    return (k4/(8*d**2) - 5*k3**2/(24*d**3)
            - k3*(2*n-3*v)/(6*d**3)
            - 3*v**2/(4*n*d**2) + 5*v**3/(6*n*d**3))


def log_saddle_carrier(n: int, t: mp.mpf, st: TiltStats) -> mp.mpf:
    mu, v = st.cumulants[1:3]
    return st.log_laplace + mu - n*mp.log(t/n) - mp.log1p(v/n)/2


def raw_moments_from_cumulants(kappa: Sequence[mp.mpf], order: int) -> list[mp.mpf]:
    if len(kappa) <= order:
        raise ValueError("insufficient cumulants")
    moments = [mp.mpf(1)]
    for r in range(1, order+1):
        moments.append(mp.fsum(comb(r-1, k-1)*kappa[k]*moments[r-k] for k in range(1,r+1)))
    return moments


def geometric_moments(n: int, q: mp.mpf) -> list[mp.mpf]:
    """Positive O(n^2) recurrence, independent of the saddle approximation."""
    q = mp.mpf(q)
    _validate(mp.mpf(1), q)
    if n < 0:
        raise ValueError("n must be nonnegative")
    m = [mp.mpf(1)]
    b = 1-q
    logq = mp.log(q)
    for r in range(1, n+1):
        c = b**r/(r+1)
        terms = []
        for k in range(r):
            terms.append(c*m[k])
            c *= (r-k+1)*q/((k+1)*b)
        m.append(mp.fsum(terms)/(-mp.expm1(r*logq)))
    return m


def geometric_moments_exact(n: int, q: Fraction) -> list[Fraction]:
    if not 0 < q < 1 or n < 0:
        raise ValueError("0<q<1 and n>=0 are required")
    m = [Fraction(1)]
    for r in range(1,n+1):
        value = sum((Fraction(comb(r,k),r-k+1)*q**k*(1-q)**(r-k)*m[k]
                     for k in range(r)), Fraction(0))
        m.append(value/(1-q**r))
    return m


def finite_moment_exact(n: int, weights: Sequence[Fraction]) -> Fraction:
    if n < 0 or not weights or any(w<=0 for w in weights) or sum(weights)!=1:
        raise ValueError("positive weights summing exactly to 1 are required")
    coef = [Fraction(1)] + [Fraction(0)]*n
    for a in weights:
        u = [a**k/factorial(k+1) for k in range(n+1)]
        coef = [sum((coef[j]*u[k-j] for j in range(k+1)), Fraction(0)) for k in range(n+1)]
    return factorial(n)*coef[n]


def equal_weight_moment_exact(n: int, m: int) -> Fraction:
    if n < 0 or m < 1:
        raise ValueError("n>=0 and m>=1 are required")
    # Stirling numbers S(n+m,m), computed by a positive integer recurrence.
    row = [1]+[0]*m
    for k in range(1,n+m+1):
        new = [0]*(m+1)
        for j in range(1,min(k,m)+1):
            new[j] = j*row[j]+row[j-1]
        row = new
    return Fraction(factorial(n)*factorial(m)*row[m], factorial(n+m)*m**n)


def critical_approximation(n: int, st: TiltStats) -> tuple[mp.mpf, mp.mpf]:
    mu, v = st.cumulants[1:3]
    leading = mp.exp(-mu**2/(2*n))
    corrected = leading*(1+v/(2*n)*(mu**2/n-1)-mu**3/(3*n**2))
    return leading, corrected
