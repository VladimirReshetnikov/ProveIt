#!/usr/bin/env python3
"""Smooth inverse diagnostics and the arbitrary fixed-order formal recurrence.

No routine here supplies an effective finite-threshold error radius. The discrete
integer threshold must be checked against exact a_n when a decision is required.
"""
import mpmath as mp
import sympy as sp
from coefficients import require


def _multiply(a, b, degree):
    return [mp.fsum(a[j] * b[r-j] for j in range(r+1))
            for r in range(degree+1)]


def _power(a, k, degree):
    result = [mp.mpf(1)] + [mp.mpf(0)] * degree
    for _ in range(k):
        result = _multiply(result, a, degree)
    return result


def _residual(alpha, u, logQ, ell, order):
    degree = order + 1
    zero = mp.mpf(0)
    v = [mp.mpf(x) for x in alpha] + [zero] * (degree+1-len(alpha))
    ev = [zero] + v[:degree]
    one_ev = ev[:]
    one_ev[0] = mp.mpf(1)
    log_one_ev = [zero] * (degree+1)
    for k in range(1, degree+1):
        power = _power(ev, k, degree)
        log_one_ev = [x + (-1)**(k+1) * y/k for x, y in zip(log_one_ev, power)]
    inside = log_one_ev[:]
    inside[0] += u-1
    lead = _multiply(_power(one_ev, 2, degree), inside, degree)
    lead[0] -= u-1
    residual = lead[1:] + [zero]
    inside = log_one_ev[:]
    inside[0] += u + mp.log(2*mp.pi)
    linear = _multiply(one_ev, inside, degree)
    residual = [a + b/2 for a, b in zip(residual, linear)]
    residual[1] += mp.mpf(1)/12 + logQ
    for r in range(1, order):
        br = ell[r]
        if r % 2 == 0:
            bernoulli = sp.bernoulli(r+2)
            br += mp.mpf(int(bernoulli.p))/int(bernoulli.q)/(r+2)/(r+1)
        inverse_power = [zero] * (degree+1)
        for k in range(degree+1):
            power = _power(ev, k, degree)
            coefficient = (-1)**k * mp.binomial(r+k-1, k)
            inverse_power = [a + coefficient*b for a, b in zip(inverse_power, power)]
        for k in range(degree-r):
            residual[k+r+1] += br * inverse_power[k]
    return residual[:order+1]


def inverse_profile_coefficients(u, Q, ell, order=2):
    """Compute alpha_0..alpha_order from the triangular formal recurrence.

    At orders zero and one ell may be []. At order >=2 use the indexed list
    [0, ell_1, ..., ell_(order-1)] (additional higher entries are ignored).
    """
    require(order >= 0 and (order <= 1 or len(ell) >= order), 'insufficient logarithmic coefficients')
    u, Q = mp.mpf(u), mp.mpf(Q)
    H = 2*u-1
    require(H != 0 and Q > 0, 'inverse profile outside its algebraic domain')
    alpha = []
    for j in range(order+1):
        residual = _residual(alpha + [mp.mpf(0)], u, mp.log(Q), ell, j)
        alpha.append(-residual[j]/H)
    return alpha


def lambert_scale(L):
    L = mp.mpf(L)
    require(L > 0, 'positive log threshold required')
    return mp.sqrt(2*L/mp.lambertw(2*L/mp.e**2))


def smooth_logarithm(x, Q, ell):
    x = mp.mpf(x)
    return x*mp.loggamma(x+1) + mp.log(Q) + mp.fsum(
        ell[r]*x**(-r) for r in range(1, len(ell)))


def smooth_root(L, Q, ell, seed=None):
    """Ordinary high-precision root on the eventual increasing large branch."""
    if seed is None:
        t = lambert_scale(L)
        seed = t + inverse_profile_coefficients(mp.log(t), Q, ell, 0)[0]
    return mp.findroot(lambda x: smooth_logarithm(x, Q, ell)-L,
                       (mp.mpf(seed)-mp.mpf('.1'), mp.mpf(seed)+mp.mpf('.1')))
