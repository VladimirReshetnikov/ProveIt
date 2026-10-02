#!/usr/bin/env python3
"""Exact fixed-sector coefficients and scaled quadrature checks.

Usage: python fixed-sector-verify.py [--order 3] [--numerics]
Requires sympy and, for quadrature, mpmath. No network or external writes.
The coefficients describe exact Taylor sectors A_{r,b}; numerical integration
uses the exponentially equivalent principal derivative integral J_{r,b}.
"""
import argparse
import json
from functools import lru_cache

import sympy as sp


def multiply(a, b, degree):
    out = [sp.S.Zero] * (degree + 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b[: degree + 1 - i]):
            out[i + j] += ai * bj
    return [sp.expand(c) for c in out]


def exponential(a, degree):
    assert a[0] == 0
    out = [sp.S.One] + [sp.S.Zero] * degree
    for n in range(1, degree + 1):
        out[n] = sp.expand(sum(k * a[k] * out[n - k]
                               for k in range(1, n + 1)) / n)
    return out


@lru_cache(None)
def coefficients(r, order):
    """Return relative rational coefficients in m=b+1 and in b."""
    r = int(r)
    n = 2 * order
    s, u, q = sp.symbols('s u q')
    s0 = sp.Rational(r, r + 1)
    lam = sp.Rational((r + 1) ** 2, r)
    harmonic = sp.harmonic(r)

    sigma = 1 / (1 - s)
    series_s = [sp.S.Zero] * (n + 1)
    for j in range(order + 1):
        derivative = sigma
        for k in range(n - 2 * j + 1):
            series_s[2 * j + k] += derivative.subs(s, s0) * u**k / sp.factorial(k)
            derivative = sp.diff(derivative, s)
        sigma = sp.cancel(-s * sp.diff(sigma, s) / (1 - s))
    power_s = [sp.S.One] + [sp.S.Zero] * n
    for _ in range(r):
        power_s = multiply(power_s, series_s, n)
    linear = [s0] + [sp.S.Zero] * n
    if n >= 1:
        linear[1] = u
    if n >= 2:
        linear[2] = -harmonic
    amplitude = multiply(linear, power_s, n)

    # phi(s)=r log(s)-(r+1)s, s=s0+u/sqrt(m).
    correction = [sp.S.Zero] * (n + 1)
    for k in range(3, n + 3):
        correction[k - 2] = sp.Rational(r * (-1) ** (k - 1), k) * (u / s0)**k
    # The Stirling series for (m!)^{-r}; its exponential can be
    # combined with the phase exponential before Gaussian integration.
    for k in range(1, order + 1):
        zpower = 4 * k - 2
        if zpower <= n:
            correction[zpower] -= r * sp.bernoulli(2 * k) / (2 * k * (2 * k - 1))
    integrand = multiply(amplitude, exponential(correction, n), n)

    def gaussian_average(poly):
        total = sp.S.Zero
        for (power,), coeff in sp.Poly(poly, u).terms():
            if power % 2 == 0:
                moment = sp.factorial2(power - 1) / lam ** (power // 2) if power else 1
                total += coeff * moment
        return sp.factor(total)

    a0 = s0 * (1 - s0) ** (-r)
    in_m = [sp.factor(gaussian_average(integrand[2 * j]) / a0)
            for j in range(order + 1)]
    p = sp.Rational(3 - r, 2)
    in_b_expression = sum(in_m[j] * q**j * (1 + q)**(p - j)
                          for j in range(order + 1))
    in_b_poly = sp.series(in_b_expression, q, 0, order + 1).removeO().expand()
    in_b = [sp.factor(in_b_poly.coeff(q, j)) for j in range(order + 1)]
    return in_m, in_b


def normalized_principal_sector(r, b, dps=70, exact=False):
    """J or exact A divided by C_r b^((3-r)/2) beta_r^b."""
    import mpmath as mp
    with mp.workdps(dps):
        m = b + 1
        beta = (mp.mpf(r) / (r + 1)) ** r
        c = (mp.mpf(r) ** (mp.mpf(r) + mp.mpf('1.5')) / (r + 1)**2
             * (2 * mp.pi) ** (mp.mpf(1 - r) / 2))
        log_scale = mp.log(c) + mp.mpf(3 - r) / 2 * mp.log(b) + b * mp.log(beta)
        h = mp.harmonic(r)

        def integrand(v):
            if not v:
                return mp.mpf(0)
            # R_b(v)=exp(v)*lower_regularized_gamma(m,v).
            lower = mp.gammainc(m, 0, v, regularized=True)
            if exact:
                q = -mp.expm1(-v)
                # This power series avoids cancellation when v is tiny.
                if v < mp.mpf('0.1'):
                    bracket = mp.hyper([1, r + 1], [r + 2], q) / (r + 1)
                else:
                    bracket = (v - sum(q**j / j for j in range(1, r + 1))) / q**(r + 1)
            else:
                bracket = v - h
            return bracket * mp.exp(-v + r * mp.log(lower) - log_scale)

        center = mp.mpf(r) * m / (r + 1)
        width = mp.sqrt(r * m) / (r + 1)
        points = sorted(set([mp.mpf(0), mp.mpf(m),
                             *[max(mp.mpf(0), center + j * width)
                               for j in (-12, -8, -4, 0, 4, 8, 12)]]))
        result = mp.quad(integrand, points + [mp.inf])
        return mp.nstr(result, 45)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--order', type=int, default=3)
    parser.add_argument('--numerics', action='store_true')
    args = parser.parse_args()
    data = {'coefficients': {}}
    for r in (1, 2, 3, 4):
        in_m, in_b = coefficients(r, args.order)
        data['coefficients'][str(r)] = {
            'relative_m_coefficients': list(map(str, in_m)),
            'relative_b_coefficients': list(map(str, in_b)),
        }
    if args.numerics:
        data['normalized_principal_sector'] = {
            str(r): {str(b): normalized_principal_sector(r, b)
                     for b in (50, 100, 200, 500)}
            for r in (2, 3)
        }
        data['normalized_exact_sector'] = {
            str(r): {str(b): normalized_principal_sector(r, b, exact=True)
                     for b in (20, 50, 100)}
            for r in (1, 2, 3)
        }
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
