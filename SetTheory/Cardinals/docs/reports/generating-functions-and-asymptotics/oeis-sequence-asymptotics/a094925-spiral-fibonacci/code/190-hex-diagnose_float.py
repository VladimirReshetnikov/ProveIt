#!/usr/bin/env python3
"""Optional mpmath fixed-order diagnostics: NO interval/error certification.

The future operator tail and amplitude are truncated at --stage. Increasing
precision alone does not remove this finite-cutoff bias. The mandatory exact
checker never imports this module or mpmath.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).absolute().parent))
from spiral import delay_table, values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', type=int, default=100)
    parser.add_argument('--dps', type=int, default=180)
    parser.add_argument('--order', type=int, default=3)
    args = parser.parse_args()
    if args.stage < 25 or args.dps < 40 or args.order < 0:
        parser.error('require stage >= 25, dps >= 40, and order >= 0')
    try:
        import mpmath as mp
    except ImportError:
        print('Optional diagnostics require mpmath; mandatory exact checks do not.', file=sys.stderr)
        return 1
    mp.mp.dps = args.dps
    phi = (1 + mp.sqrt(5)) / 2
    q, rho, alpha = phi ** -6, -phi ** -2, phi / mp.sqrt(5)
    rows = delay_table(args.stage)
    sequence = values(rows)
    nmax = len(rows) - 1
    c = (mp.mpf(sequence[-1]) * phi + mp.mpf(sequence[-2])) * phi ** -nmax / mp.sqrt(5)
    weights = [[(j, phi ** (j - n)) for j in row] for n, row in enumerate(rows)]

    def apply_operator(f):
        forcing = [sum((w * f[j] for j, w in row), mp.mpf(0)) for row in weights]
        result = [mp.mpf(0)] * len(rows)
        future = mp.mpf(0)
        for n in range(nmax, -1, -1):
            result[n] = -alpha * future
            future += forcing[n]
        past = mp.mpf(0)
        for n in range(nmax + 1):
            past = rho * past + forcing[n]
            result[n] += past / (phi * mp.sqrt(5))
        return result

    coefficients = [[mp.mpf(1)] * len(rows)]
    for _ in range(args.order):
        coefficients.append(apply_operator(coefficients[-1]))
    checks = []
    for r in [4, 8, 12, 16, 20]:
        start = 3 * r * r - 2 * r + 2
        for n in [start, start + r // 2, start + 3 * r, start + 5 * r + 1, start + 6 * r]:
            actual = mp.mpf(sequence[n]) * phi ** -n / c
            cumulative, errors, scaled = mp.mpf(0), [], []
            for order in range(args.order + 1):
                cumulative += coefficients[order][n]
                error = actual - cumulative
                errors.append(mp.nstr(error, 16))
                scaled.append(mp.nstr(error / (r ** (order + 1) * q ** ((order + 1) * r)), 16))
            checks.append({'r': r, 'n': n, 'errors_J0_through_requested_order': errors,
                           'errors_scaled_by_next_stage_order': scaled})
    print(json.dumps({'status': 'DIAGNOSTIC_ONLY', 'interval_certified': False,
                      'precision_digits': args.dps, 'cutoff_stage': args.stage,
                      'cutoff_N': nmax, 'fixed_order': args.order,
                      'amplitude_approximation': mp.nstr(c, min(120, args.dps - 10)),
                      'scope': 'Floating finite-cutoff experiments only. No rounding-safe '
                               'bounds, asymptotic onset, or growing-order theorem is certified.',
                      'checks': checks}, sort_keys=True, indent=2))
    return 0


if __name__ == '__main__':
    sys.exit(main())
