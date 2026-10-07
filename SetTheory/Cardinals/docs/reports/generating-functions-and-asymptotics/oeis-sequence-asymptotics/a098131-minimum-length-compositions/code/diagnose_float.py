#!/usr/bin/env python3
"""Optional mpmath diagnostics. Never called by build.py or reproduce.py.

These are floating experiments, not certified enclosures or proofs of error
bounds, onset thresholds, exact inverse rounding, or uniformity in growing s.
Install mpmath separately if wanted. Output is JSON on stdout only.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).absolute().parent))
from compositions import a_count, b_count
from coefficients import coefficients


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=1000000,
                        help='largest point from 1000,10000,100000,1000000 (default 1000000)')
    parser.add_argument('--dps', type=int, default=80)
    args = parser.parse_args()
    if not 1000 <= args.max_n <= 1000000 or not 40 <= args.dps <= 200:
        parser.error('require 1000<=max-n<=1000000 and 40<=dps<=200')
    try:
        import mpmath as mp
    except ImportError:
        parser.error('optional dependency mpmath is not installed')
    mp.mp.dps = args.dps

    def evaluate(v, s, order):
        return [mp.mpf(c.numerator) / c.denominator
                for c in coefficients(Fraction(str(v)), s, order)]

    def log_lead(v, s):
        return mp.exp(v) * v * (v + 1) / 2 - mp.mpf(3 + 2 * s) * v / 4 - mp.log(v * v + 3 * v + 1) / 2

    def coordinate(n):
        v = mp.findroot(lambda w: 2 * w + mp.log(w) + mp.log(w + 2) - mp.log(4 * n),
                        (mp.log(n) / 4, mp.log(n) / 2))
        return v, mp.exp(-v)

    forward, inverse = [], []
    for n in (1000, 10000, 100000, 1000000):
        if n > args.max_n:
            continue
        v, t = coordinate(n)
        approximations = {}
        for s in (0, 1, 2, 5):
            exact = a_count(n, s)
            cs = evaluate(v, s, 3)
            lead = mp.exp(log_lead(v, s))
            values = [lead * sum(t ** j * cs[j] for j in range(order + 1)) for order in range(4)]
            approximations[s] = values
            forward.append({'n': n, 's': s, 'type': 'a', 'v': str(v),
                            'relative_errors': [str(value / exact - 1) for value in values]})
            v0 = mp.findroot(lambda w: log_lead(w, s) - mp.log(exact), v)
            x0 = mp.exp(2 * v0) * v0 * (v0 + 2) / 4
            inverse.append({'n': n, 's': s, 'uncorrected_index_error': str(x0 - n),
                            'corrected_index_error': str(x0 - evaluate(v0, s, 1)[1] - n),
                            'remainder_scale': str(mp.exp(-v0) * (1 + v0) ** 2)})
        forward.append({'n': n, 's': 0, 'type': 'b',
                        'relative_errors': [str((left - right) / b_count(n) - 1)
                                            for left, right in zip(approximations[0], approximations[1])]})
    print(json.dumps({'status': 'diagnostic', 'certified': False, 'precision_decimal_digits': args.dps,
                      'dependency': 'mpmath', 'dependency_version': mp.__version__,
                      'forward': forward, 'inverse': inverse}, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
