#!/usr/bin/env python3
"""Uniform restricted-partition profiles; numerical, not interval-certified.

All arguments and logarithms use mpmath. No external data or network needed.
"""
from __future__ import annotations
import mpmath as mp


def h(s):
    s = mp.mpf(s)
    if not s:
        return mp.mpf(0)
    return mp.log(s / (2 * mp.sinh(s / 2)))


def H(s):
    s = mp.mpf(s)
    if not s:
        return mp.mpf(0)
    if abs(s) < mp.mpf('0.5'):
        total = mp.mpf(0)
        for k in range(1, 200):
            term = -mp.bernpoly(2*k, 0)*s**(2*k)/(2*k*mp.factorial(2*k)*(2*k+1))
            total += term
            if abs(term) < mp.eps * max(mp.mpf(1), abs(total)):
                return total
        raise ArithmeticError('H power series did not converge')
    return mp.log(s)-1-s/4+(mp.pi**2/6-mp.polylog(2, mp.exp(-s)))/s


def B(s):
    return 1-h(s)+H(s)


def bisect_increasing(f, target, upper=1):
    lo, hi = mp.mpf(0), mp.mpf(upper)
    for _ in range(200):
        if f(hi) >= target:
            break
        hi *= 2
    else:
        raise ArithmeticError('Could not bracket inverse')
    for _ in range(mp.mp.prec + 10):
        mid = (lo+hi)/2
        if f(mid) < target:
            lo = mid
        else:
            hi = mid
    return (lo+hi)/2


def saddle(epsilon):
    eps = mp.mpf(epsilon)
    if not 0 <= eps < 4:
        raise ValueError('epsilon must lie in [0,4)')
    if not eps:
        return mp.mpf(0)
    # Newton, with a monotone bisection fallback.
    guess = eps/(1-eps/4)
    try:
        s = mp.findroot(lambda z: z/B(z)-eps, (eps, guess),
                        solver='secant', tol=mp.eps*100, maxsteps=40)
        if s > 0 and abs(s/B(s)-eps) < mp.sqrt(mp.eps):
            return s
    except (ValueError, ArithmeticError, ZeroDivisionError, TypeError):
        pass
    return bisect_increasing(lambda z: z/B(z) if z else mp.mpf(0), eps)


def profiles_from_s(s):
    s = mp.mpf(s)
    if not s:
        return (mp.mpf(0),)*4
    b = B(s)
    eps = s/b
    hp, hpp = mp.diff(h, s), mp.diff(h, s, 2)
    q2 = 1+s*s*mp.diff(H, s, 2)
    q3 = -2+s**3*mp.diff(H, s, 3)
    q4 = 6+s**4*mp.diff(H, s, 4)
    d = b-1-mp.log(b)+H(s)
    e0 = h(s)/2+mp.log(b)-mp.log(q2)/2
    e1 = (mp.mpf(1)/12+s*hp/12
          -(hpp/2+hp*hp/4)*s*s/(2*q2)
          +hp*s*q3/(4*q2*q2)+q4/(8*q2*q2)
          -5*q3*q3/(24*q2**3))
    return eps, d, e0, e1


def log_volume(m, x):
    return (m-1)*mp.log(x)-mp.loggamma(m+1)-mp.loggamma(m)


def log_uniform(m, n, order=1):
    if m < 2 or n < 1 or order not in (-1, 0, 1):
        raise ValueError('Require m>=2, n>=1, order in {-1,0,1}')
    x = mp.mpf(n)+mp.mpf(m*(m+1))/4
    eps, d, e0, e1 = profiles_from_s(saddle(mp.mpf(m*m)/x))
    result = log_volume(m, x)+m*d
    if order >= 0:
        result += e0
    if order >= 1:
        result += e1/m
    return result


def exact_saddle_log(m, n, correction=True):
    """Finite-sum saddle, optionally with its first Edgeworth correction."""
    def mean(t):
        return mp.fsum(j/mp.expm1(j*t) for j in range(1, m+1))
    lo, hi = mp.mpf(0), mp.mpf(m)/n
    for _ in range(mp.mp.prec+10):
        mid = (lo+hi)/2
        if mean(mid) > n:
            lo = mid
        else:
            hi = mid
    t = (lo+hi)/2
    k2 = k3 = k4 = mp.mpf(0)
    L = mp.mpf(0)
    for j in range(1, m+1):
        q = mp.exp(-j*t)
        den = -mp.expm1(-j*t)
        L -= mp.log(den)
        k2 += j**2*q/den**2
        k3 += j**3*q*(1+q)/den**3
        k4 += j**4*q*(1+4*q+q*q)/den**4
    ans = n*t+L-mp.log(2*mp.pi*k2)/2
    if correction:
        c1 = k4/(8*k2*k2)-5*k3*k3/(24*k2**3)
        ans += mp.log1p(c1)
    return ans


def inverse_from_log(m, log_y, corrected=True):
    """Approximate centered X at a sample value; no exact integer rounding."""
    z = mp.exp((log_y+mp.loggamma(m+1)+mp.loggamma(m))/(m-1))
    eta = mp.mpf(m*m)/z
    def eta_of_s(s):
        if not s:
            return mp.mpf(0)
        b = B(s)
        d = b-1-mp.log(b)+H(s)
        return s/b*mp.exp(-d)
    # This parametrization covers eta in (0,e^2), corresponding to eps<4.
    if not 0 < eta < mp.e**2:
        raise ValueError('This inverse chart requires 0<eta<e^2')
    s = bisect_increasing(eta_of_s, eta)
    eps, d, e0, _ = profiles_from_s(s)
    R = mp.exp(-d)
    v = (-d-e0)/B(s)
    return z*R*(mp.exp(v/m) if corrected else 1)
