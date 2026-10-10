#!/usr/bin/env python3
"""Independent high-index axis diagnostics; floating-point evidence, not a certificate.

The quadrature integrates K_N(exp(-t))-1 directly with expm1, so it does
not subtract two quantities close to one after integration.  Arbitrary
N is supported without constructing an Euler sum of length N.
"""

import argparse
import json
from pathlib import Path
import mpmath as mp


def constants():
    d = mp.log(mp.mpf(3) / 2)
    p = mp.log(2) / d
    q = mp.log(3) / mp.log(2)
    c = (1 - 1 / q) * q ** (-p)
    delta = mp.log(mp.mpf(10) / 9) / d
    return d, p, q, c, delta


def axis_excess(n, b, order=0):
    """D_N(b) or its first two b derivatives, using the gamma score."""
    n = mp.mpf(n)
    psi = mp.digamma(b)
    tri = mp.polygamma(1, b)
    loggamma = mp.loggamma(b)

    def integrand(t):
        if t <= 0 or not mp.isfinite(t):
            return mp.mpf(0)
        u = mp.exp(-t)
        if u == 1:
            excess = -mp.mpf(1) if n > 1 else mp.mpf(0)
        else:
            logk = mp.log1p(u) + (n - 1) * mp.log1p(-u*u) - mp.log1p(u*u)
            excess = mp.expm1(logk)
        density = mp.exp((b - 1) * mp.log(t) - t - loggamma)
        score = mp.log(t) - psi
        factor = [mp.mpf(1), score, score*score - tri][order]
        return density * excess * factor

    ell = mp.log(n)
    finite = sorted(set([mp.mpf(0), mp.mpf(1), ell / 2,
                         b / 3, ell, b / 2, b, 2*b]))
    finite = [t for t in finite if t >= 0]
    return mp.quad(integrand, finite + [mp.inf])


def one(n):
    d, p, q, c, delta = constants()
    center = mp.log(n*q)/d
    maximum_b = mp.findroot(lambda b: axis_excess(n, b, 1),
                            (center-mp.mpf('.3'), center+mp.mpf('.3')),
                            tol=mp.power(10, -(mp.mp.dps - 15)))
    excess = axis_excess(n, maximum_b)
    curvature = axis_excess(n, maximum_b, 2)
    center_excess = axis_excess(n, center)
    lower = mp.power(2, -center) - n*mp.power(3, -center) - n*mp.power(4, -center)
    upper = lower + (n*n-n+2)/2 * (mp.power(5, -center)+mp.power(6, -center))
    assert lower <= center_excess <= upper
    assert curvature < 0
    conv = lambda z: mp.nstr(z, 40)
    return dict(N=int(n), asymptotic_center=conv(center), stationary_b=conv(maximum_b),
                center_shift=conv(maximum_b-center), scaled_excess=conv(excess/(c*n**(-p))),
                axis_excess=conv(excess), second_derivative=conv(curvature),
                center_taylor_lower=conv(lower), center_taylor_value=conv(center_excess),
                center_taylor_upper=conv(upper))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dps', type=int, default=65)
    parser.add_argument('--indices', nargs='+', type=int,
                        default=[10, 100, 1000, 10000, 1000000, 100000000])
    parser.add_argument('--output', default='axis_large_n_diagnostics.json')
    args = parser.parse_args()
    mp.mp.dps = args.dps
    d,p,q,c,delta = constants()
    rows = []
    for n in args.indices:
        row = one(mp.mpf(n))
        rows.append(row)
        print(json.dumps(row), flush=True)
    receipt = dict(status='numerical diagnostic, not an interval certificate',
                   method='direct gamma quadrature of expm1(log K_N)',
                   mpmath_version=mp.__version__, decimal_precision=args.dps,
                   p=mp.nstr(p,50), c=mp.nstr(c,50), delta=mp.nstr(delta,50), rows=rows)
    Path(args.output).write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
