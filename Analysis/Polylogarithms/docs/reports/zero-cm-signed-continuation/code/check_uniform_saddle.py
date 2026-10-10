#!/usr/bin/env python3
"""Numerical diagnostics for the proved uniform moving-saddle expansion.

The quadrature is of the exact positive Mellin integral.  These floating-point
comparisons check formulas and scaling; they are not interval certificates.
Run from any directory; outputs go to ../results/.
"""
from pathlib import Path
import argparse
import csv
import json
import mpmath as mp


def L(x):
    return mp.log1p(mp.exp(-x))


def H(x):
    t = mp.exp(-x)
    return mp.log(mp.log1p(t) / t)


def w(x):
    t = mp.exp(-x)
    return 1 / ((1 + t) * (mp.log1p(t) / t))


def saddle(p, h, a):
    p, h, a = map(mp.mpf, (p, h, a))
    lo = p / (h + a)
    hi = p / (h / (2 * mp.log(2)) + a)
    for _ in range(4 * mp.mp.dps):
        mid = (lo + hi) / 2
        if mid * (h * w(mid) + a) < p:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def evaluate(p, h, a):
    p, h, a = map(mp.mpf, (p, h, a))
    x = saddle(p, h, a)
    theta = h * x / p
    B = 1 + theta * x * mp.diff(w, x)
    b3 = 2 - theta * x**2 * mp.diff(w, x, 2)
    b4 = -6 - theta * x**3 * mp.diff(w, x, 3)
    v = 1 / (1 + mp.exp(x))
    ell1 = -1 + x * v
    ell2 = 1 - x*x*v*(1-v)
    c1 = ((ell2 + ell1**2) / (2*B) + b3*ell1/(2*B**2)
          + b4/(8*B**2) + 5*b3*b3/(24*B**3))
    d1 = c1 - mp.mpf(1)/12
    delta = (h + a) * x / p - 1
    E = p*(mp.log1p(delta) - delta) + h*H(x)
    logA = E - mp.log1p(mp.exp(-x)) - mp.log(B)/2

    # Exact transformed Mellin integral, with no saddle-series truncation.
    # Centering at x is solely a quadrature conditioning choice.
    Hp = 1 - w(x)
    def phi(u):
        return (mp.log(u) - u + 1 + theta/x
                * (H(x*u) - H(x) - x*Hp*(u-1)))
    rootp = mp.sqrt(p)
    def integrand(z):
        u = 1 + z/rootp
        if u <= 0:
            return mp.mpf(0)
        return mp.exp(p*phi(u)) / (u*(1+mp.exp(-x*u)))
    # The global gamma-phase bound makes these tail breakpoints reliable.
    breaks = sorted(set([-rootp, -min(rootp/2, mp.mpf(8)),
                         -min(rootp/4, mp.mpf(3)), mp.mpf(0),
                         mp.mpf(3), mp.mpf(8), mp.mpf(20)]))
    integral = mp.quad(integrand, breaks + [mp.inf]) / rootp
    log_star = (mp.loggamma(p) - (p-mp.mpf('0.5'))*mp.log(p)
                + p - mp.log(2*mp.pi)/2)
    ratio = (integral * (1+mp.exp(-x)) * mp.sqrt(p*B/(2*mp.pi))
             * mp.exp(-log_star))
    return dict(p=p, h=h, a=a, alpha=p/h, x=x, B=B, log_A=logA,
                log_R=logA+mp.log(ratio), d1=d1,
                ratio_to_leading=ratio, leading_relative_error=1/ratio-1,
                corrected_relative_error=(1+d1/p)/ratio-1,
                p2_corrected_error=p*p*((1+d1/p)/ratio-1))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dps', type=int, default=70)
    parser.add_argument('--quick', action='store_true')
    args = parser.parse_args()
    mp.mp.dps = args.dps
    cases = []
    hs = (25, 100) if args.quick else (25, 100, 400)
    for h in hs:
        for alpha in (mp.mpf('0.2'), mp.mpf(1), mp.log(h)-1,
                      mp.log(h), mp.log(h)+2, mp.mpf(20)):
            cases.append((h*alpha, h, mp.mpf('0.5')))
    if not args.quick:
        cases += [(100, 100000, mp.mpf('0.5')), (400, 1000000, 100),
                  (100, 1, mp.mpf('0.5')), (400, 1, mp.mpf('0.5')),
                  (100, 50, 10000), (400, 50, 10000)]
    rows = []
    for case in cases:
        row = evaluate(*case)
        rows.append({key: mp.nstr(val, 45) for key, val in row.items()})
        print('p=%s h=%s a=%s corrected relative error=%s'
              % (mp.nstr(row['p'], 7), mp.nstr(row['h'], 7),
                 mp.nstr(row['a'], 7), mp.nstr(row['corrected_relative_error'], 8)))
    out = Path(__file__).resolve().parent.parent / 'results'
    out.mkdir(parents=True, exist_ok=True)
    (out/'uniform_saddle.json').write_text(json.dumps(
        {'working_decimal_digits': args.dps, 'status': 'numerical diagnostic',
         'cases': rows}, indent=2)+'\n')
    with (out/'uniform_saddle.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)


if __name__ == '__main__':
    main()
