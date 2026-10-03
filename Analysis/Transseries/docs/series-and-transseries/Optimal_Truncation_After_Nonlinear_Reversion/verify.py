#!/usr/bin/env python3
"""High-precision checks of direct inverse-harmonic optimal truncation.

Dependencies: mpmath.  Results are numerical checks, NOT interval certificates.
Run: python verify.py --max-order 240 --output results.csv
"""
from __future__ import annotations
import argparse
import csv
import math
import time
from pathlib import Path
import mpmath as mp


def coefficients(nmax: int) -> tuple[list[mp.mpf], list[mp.mpf]]:
    """Lagrange coefficient extraction by a triangular exponential recurrence."""
    c = [mp.mpf(0)] + [-(mp.power(2, 1-2*j)-1)*mp.bernoulli(2*j)/(2*j)
                         for j in range(1, nmax+1)]
    h = [mp.mpf(1)]
    for n in range(1, nmax+1):
        s = 2*n-1
        a = [mp.mpf(1)]
        for k in range(1, n+1):
            a.append(s*mp.fsum(j*c[j]*a[k-j] for j in range(1, k+1))/k)
        h.append(-a[n]/s)
    return c, h


def polynomial_at_inverse_square(c: list[mp.mpf], w: mp.mpf, m: int) -> mp.mpf:
    z = 1/w**2
    value = mp.mpf(0)
    for j in range(m, 0, -1):
        value = (value+c[j])*z
    return value


def correction1(s: mp.mpf) -> mp.mpf:
    return -mp.pi/12+(2*s*s-3*s+mp.mpf(7)/12)/(2*mp.pi)


def correction2(s: mp.mpf) -> mp.mpf:
    return (s**4/(2*mp.pi**2)-11*s**3/(6*mp.pi**2)
            -s**2/12+5*s**2/(3*mp.pi**2)+s/(48*mp.pi**2)
            +5*s/24-mp.mpf(43)/288-mp.mpf(203)/(1152*mp.pi**2)
            +mp.pi**2/288)


def run_case(m: int, sigma: mp.mpf, c: list[mp.mpf], h: list[mp.mpf]) -> dict[str, str]:
    x = (m+1-sigma)/mp.pi
    w = mp.findroot(lambda v: mp.digamma(v+mp.mpf('0.5'))-mp.log(x),
                    (x-1/(12*x), x), solver='secant', tol=mp.eps*128)
    p = x+mp.fsum(h[j]*x**(1-2*j) for j in range(1, m+1))
    um = w
    for _ in range(6):
        residual = mp.log(um/x)+polynomial_at_inverse_square(c, um, m)
        slope = 1/um-mp.fsum(2*j*c[j]*um**(-2*j-1) for j in range(1, m+1))
        um -= residual/slope
    scale = (-1)**m*mp.sqrt(x)*mp.exp(-2*mp.pi*x)
    ratio = (p-w)/scale
    cut = (um-p)/scale
    d1, d2 = correction1(sigma), correction2(sigma)
    next_term = h[m+1]*x**(-2*m-1)
    theta = mp.mpf('0.5')+(1-4*sigma)/(8*mp.pi*x)
    improved = p+theta*next_term
    # The residual check is independent of the coefficient extraction.
    assert abs(mp.digamma(w+mp.mpf('0.5'))-mp.log(x)) < mp.power(10, -mp.mp.dps+15)
    assert ratio > 0
    vals = {
        'M': m, 'sigma': sigma, 'X': x,
        'direct_scaled_error': ratio,
        'X_times_ratio_minus_1': x*(ratio-1), 'D1_predicted': d1,
        'second_scaled_residual': x*x*(ratio-1-d1/x), 'D2_predicted': d2,
        'third_scaled_residual': x**3*(ratio-1-d1/x-d2/x**2),
        'X_times_cutoff_error': x*cut, 'cutoff_first_limit': mp.pi/6,
        'cutoff_second_residual': x*x*(cut-mp.pi/(6*x)),
        'cutoff_second_limit': sigma**2/6-sigma/4+mp.mpf(25)/144,
        'midpoint_scaled_error': x*((p+next_term/2-w)/scale),
        'midpoint_limit': (1-4*sigma)/(4*mp.pi),
        'corrected_scaled_error': x*x*(improved-w)/scale,
        'absolute_direct_error': abs(p-w),
        'absolute_corrected_error': abs(improved-w),
    }
    return {key: str(value) if isinstance(value, int) else mp.nstr(value, 24)
            for key, value in vals.items()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-order', type=int, default=240)
    parser.add_argument('--output', type=Path, default=Path('results.csv'))
    args = parser.parse_args()
    if args.max_order < 30:
        parser.error('--max-order must be at least 30')
    mp.mp.dps = math.ceil(2*(args.max_order+3)/math.log(10))+100
    print(f'Precision: {mp.mp.dps} decimal digits', flush=True)
    start = time.monotonic()
    c, h = coefficients(args.max_order+1)
    print(f'Coefficients complete in {time.monotonic()-start:.1f}s', flush=True)
    orders = [m for m in [30,60,120,180,240] if m <= args.max_order]
    cases = [(m,mp.mpf('0.75')) for m in orders]
    m = orders[-1]
    cases.extend([(m,mp.mpf('-0.5')), (m,mp.mpf('0.25')), (m,mp.mpf('1.25'))])
    rows = []
    for m, sigma in cases:
        row = run_case(m, sigma, c, h)
        rows.append(row)
        print('M=',m,'sigma=',sigma,'R=',row['direct_scaled_error'],
              'D2 check=',row['second_scaled_residual'],
              'vs',row['D2_predicted'], flush=True)
    with args.output.open('w', newline='') as out:
        # ed. (2026-09-29): LF line endings on every platform, like the filed file.
        writer=csv.DictWriter(out,fieldnames=list(rows[0]),lineterminator='\n')
        writer.writeheader(); writer.writerows(rows)
    print(f'Wrote {args.output}; elapsed {time.monotonic()-start:.1f}s', flush=True)

if __name__ == '__main__':
    main()
