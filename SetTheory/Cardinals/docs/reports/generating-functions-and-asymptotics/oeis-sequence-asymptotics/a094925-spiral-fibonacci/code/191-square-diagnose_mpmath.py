#!/usr/bin/env python3
"""Optional non-certifying high-precision diagnostics; never imported by a build.

Requires a separately installed mpmath. Finite numerical output gives no
certified amplitude digits, effective asymptotic onset, or uniform error bound.
"""
from __future__ import annotations
import argparse
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).absolute().parent))
from spiral import integer, predecessor


def run(max_n, precision):
    integer(max_n, 100, 1000000, 'maximum index')
    integer(precision, 30, 200, 'decimal working precision')
    # Intentionally lazy and confined to this optional executable.
    import mpmath as mp
    mp.mp.dps = precision

    def components(n):
        r = mp.sqrt(n)
        w = mp.lambertw(4*r)
        theta = mp.frac(2*r)
        h = r/2*(w-1+1/w) + w*w/32 + w/2 - mp.log1p(w)/2
        xi = w*w/(16*r)*(theta*theta-theta+mp.mpf(1)/6)
        return r, w, h, xi

    logs = [mp.ninf, mp.mpf(0)]
    marks = {100, 1000, 10000, 100000, 1000000, max_n}
    samples = []
    for n in range(2, max_n+1):
        logs.append(logs[-1]+mp.log1p(mp.exp(logs[predecessor(n)]-logs[-1])))
        if n in marks:
            r, w, h, xi = components(n)
            samples.append({'n': n, 'log_a_minus_H': mp.nstr(logs[n]-h, 20),
                            'log_a_minus_H_minus_Xi': mp.nstr(logs[n]-h-xi, 20),
                            'w3_over_r': mp.nstr(w**3/r, 20)})
    residuals = []
    for k in (100, 101, 1000, 1001, 10000, 10001, 1000000, 1000001):
        q, length = k*k//4, (k+1)//2
        off, exceptional = [], []
        for j in sorted({0, 1, 2, 3, length//4, length//2, 3*length//4, length-2, length-1}):
            if not 0 <= j < length:
                continue
            n = q+j
            # The exact formula is unbounded mathematically; avoid the bounded
            # recurrence API because these diagnostic sample indices are huge.
            index_k = isqrt(4*n+1)
            t = n-2*index_k+3+int(n == index_k*index_k//4)
            r, w, h, xi = components(n)
            f = h+xi
            _, _, hp, xp = components(n-1)
            _, _, ht, xt = components(t)
            defect = -mp.expm1(hp+xp-f)-mp.exp(ht+xt-f)
            (exceptional if j in (0, 1) else off).append(
                abs(defect)*(r*r/(w*w) if j in (0, 1) else r**3/w**3))
        residuals.append({'side_k': k,
                          'off_exception_scaled_max': mp.nstr(max(off), 20),
                          'exception_scaled_max': mp.nstr(max(exceptional), 20)})
    return {'status': 'DIAGNOSTIC_ONLY', 'working_decimal_digits': precision,
            'max_n': max_n, 'arithmetic': 'mpmath noninterval arbitrary precision',
            'warning': 'No certified amplitude digits, remainder constants, or effective onset',
            'normalization_samples': samples, 'residual_samples': residuals}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=10000)
    parser.add_argument('--precision', type=int, default=80)
    args = parser.parse_args()
    try:
        print(json.dumps(run(args.max_n, args.precision), sort_keys=True, indent=2))
    except (ValueError, ImportError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
