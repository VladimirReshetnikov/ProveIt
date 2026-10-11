#!/usr/bin/env python3
"""End-to-end diagnostic for the explicit sixth digamma moment.

The left side uses a convergent Laurent series plus ordinary quadrature.
Each height-one Laurent slope is evaluated by its independent subtracted
Mellin integral.  Omega_5 is read from the separately reproduced residue
series audit, never obtained by rearranging the proposed sixth identity.
Floating-point residuals are diagnostics, not certified error bounds.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]


def reciprocal_gamma_coefficients(order):
    c = [mp.mpf(1)]
    for n in range(1, order + 1):
        c.append((mp.euler * c[n-1] + mp.fsum(
            (-1)**(k+1) * mp.zeta(k) * c[n-k]
            for k in range(2, n+1))) / n)
    return c


def height_one_slope(d, c):
    # For v=exp(-y), -log(1-exp(-v))=y+delta.  Expand the difference
    # of d-th powers exactly as a finite binomial sum to avoid cancellation.
    log_coeffs = [-mp.bernoulli(2*k)/(2*k*mp.factorial(2*k))
                  for k in range(1, 41)]

    def small_v_delta(v):
        if v > mp.mpf('0.1'):
            return -mp.log(-mp.expm1(-v)/v)
        return v/2 + mp.fsum(a*v**(2*k)
                             for k, a in enumerate(log_coeffs, 1))

    def transformed(y):
        delta = small_v_delta(mp.exp(-y))
        return mp.fsum(mp.binomial(d, j)*y**(d-j)*delta**j
                       for j in range(1, d+1))

    lower = mp.quad(transformed, [0, 1, 3, 8, mp.inf])
    upper = mp.quad(lambda v: (-mp.log1p(-mp.exp(-v)))**d/v,
                    [1, 2, 5, mp.inf])
    return c[d+1] + (lower + upper)/mp.factorial(d)


def raw_finite_part(m, split, degree):
    base = [-mp.mpf(1), -mp.euler]
    base.extend((-1)**k * mp.zeta(k) for k in range(2, degree+1))
    product = [mp.mpf(1)] + [mp.mpf(0)]*degree
    for _ in range(m):
        product = [mp.fsum(product[j]*base[k-j] for j in range(k+1))
                   for k in range(degree+1)]
    local = mp.fsum(a*(mp.log(split) if k == m-1 else
                      split**(k-m+1)/(k-m+1))
                    for k, a in enumerate(product))
    ordinary = mp.quad(lambda x: mp.digamma(x)**m,
                       [split, mp.mpf('0.25'), mp.mpf('0.5'), 1])
    return local + ordinary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dps', type=int, default=90)
    parser.add_argument('--mixed-report', type=Path,
                        default=ROOT/'verification/mixed_sixth_audit.json')
    parser.add_argument('--output', type=Path,
                        default=ROOT/'verification/sixth_moment.json')
    args = parser.parse_args()
    mp.mp.dps = args.dps
    mixed = json.loads(args.mixed_report.read_text())
    omega = mp.mpf(mixed['residue_coordinate'])
    c = reciprocal_gamma_coefficients(6)
    lam = {}
    for d in range(1, 6):
        lam[d] = height_one_slope(d, c)
        print('lambda_' + str(d) + ' = ' + mp.nstr(lam[d], 35), flush=True)
    g = mp.euler
    z = {n: mp.zeta(n) for n in range(2, 7)}
    rhs = (15*omega - 720*lam[5] + 720*g*lam[4] - 720*c[2]*lam[3]
           + 720*c[3]*lam[2] + 720*c[4]*mp.stieltjes(1)
           - 60*g**3*z[2] + 180*g**2*z[3] - 70*g*z[4]
           - 55*z[2]*z[3] + 175*z[5] + 48*mp.diff(mp.zeta, 5)
           - 135*z[6])
    lhs = raw_finite_part(6, mp.mpf(1)/8, 150)
    lhs_other = raw_finite_part(6, mp.mpf(1)/10, 140)
    report = {
        'precision_digits': args.dps,
        'coordinate': 'original x cutoff; constant of integral from epsilon to 1',
        'omega_source': args.mixed_report.name,
        'lambda_evaluation': 'independent subtracted Mellin integral',
        'lambda_values': {str(d): mp.nstr(lam[d], args.dps) for d in lam},
        'lambda1_sign_control': mp.nstr(lam[1]+mp.stieltjes(1), args.dps),
        'sixth_moment_left': mp.nstr(lhs, args.dps),
        'sixth_moment_right': mp.nstr(rhs, args.dps),
        'identity_residual': mp.nstr(lhs-rhs, args.dps),
        'two_split_quadrature_difference': mp.nstr(lhs-lhs_other, args.dps),
        'diagnostic_only': True,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print('Q6 =', mp.nstr(lhs, 60), flush=True)
    print('identity residual =', mp.nstr(lhs-rhs, 12), flush=True)
    print('two-split difference =', mp.nstr(lhs-lhs_other, 12), flush=True)


if __name__ == '__main__':
    main()
