#!/usr/bin/env python3
"""Certify N_(1/e)(1000)=6207 by exact integer arithmetic.

The inverse expansion suggests two candidates but is not used in the
certificate. A rational enclosure of e and exact counting sums decide them.
No third-party packages are required (the row recurrence is repeated here).
"""
from __future__ import annotations
from fractions import Fraction
from math import factorial
from pathlib import Path
import json


def ordered_stirling_row(m: int) -> list[int]:
    if m < 1:
        raise ValueError('m must be positive')
    row = [1]
    for h in range(1, m + 1):
        row = [0] + [k * ((row[k] if k < len(row) else 0) + row[k-1])
                     for k in range(1, h + 1)]
    return row


def main() -> None:
    m, N, cutoff = 1000, 6207, 30
    lower = sum((Fraction(1, factorial(k)) for k in range(cutoff + 1)), Fraction(0))
    # The first omitted term is 1/(cutoff+1)!, with subsequent ratios
    # at most 1/(cutoff+2). A geometric bound therefore gives upper > e.
    upper = lower + Fraction(cutoff + 2, (cutoff + 1)*factorial(cutoff + 1))
    row = ordered_stirling_row(m)
    mf = factorial(m)
    tests = []
    for n, target, side in [(N-1, upper, 'R > e'), (N, lower, 'R < e')]:
        numerator = sum(row[k] * k**n for k in range(1, m+1))
        denominator = mf * m**n
        comparison = numerator * target.denominator - denominator * target.numerator
        assert (comparison > 0) if n == N-1 else (comparison < 0)
        tests.append({'n': n, 'proved': side, 'comparison_sign': 1 if comparison > 0 else -1,
                      'numerator_bit_length': numerator.bit_length(),
                      'denominator_bit_length': denominator.bit_length()})
    report = {'status': 'PASS', 'm': m, 'target_probability': '1/e',
              'certified_integer_threshold': N, 'exponential_series_cutoff': cutoff,
              'e_lower': str(lower), 'e_upper': str(upper), 'exact_comparisons': tests,
              'method': 'Exact integer counts and a rational enclosure of e; no floating point.'}
    data = Path(__file__).resolve().parents[1] / 'data'
    data.mkdir(exist_ok=True)
    (data / 'threshold_certificate.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
