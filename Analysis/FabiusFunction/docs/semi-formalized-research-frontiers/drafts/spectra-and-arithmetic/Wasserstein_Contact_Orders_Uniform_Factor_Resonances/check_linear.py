#!/usr/bin/env python3
"""Finite floating-point regressions, not proofs or optimal-distance calculations."""
import cmath
import json
import math

# ed. (2026-10-01): the receipt printed below is also written to
# <output-dir>/linear-verification.json, by default rerun/ beside this program, with LF line
# endings (as delivered it went only to standard output, and a shell
# redirection on Windows writes CRLF). Pass --output-dir with this program's
# own directory, on a copy, to regenerate the recorded receipt.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))


def sinc(x):
    return 1.0 if x == 0 else math.sin(x) / x


def product(q, frequency, start=2, stop=100):
    return math.prod(sinc(math.pi * frequency * q**k) for k in range(start, stop))


def source_derivative(q):
    # The exact-zero first source factor was differentiated analytically.
    return sinc(6 * math.pi * q) * product(q, 6) / 6


counts = {'compact_source_pairs': 0, 'defect_ratios': 0, 'bound_grid': 0}
for radius in [0, 0.5, 1, 2]:
    for frequency in [0, -6, 0.125, 6, 100]:
        for x in [-radius, -radius / 2, 0, radius / 2, radius]:
            for y in [-1000, -5, -0.1, 0, 0.1, 5, 1000]:
                lhs = abs(x * cmath.exp(2j * math.pi * frequency * x)
                          - y * cmath.exp(2j * math.pi * frequency * y))
                rhs = (1 + 2 * math.pi * abs(frequency) * radius) * abs(x - y)
                assert lhs <= rhs + 1e-10 * (1 + rhs)
                counts['compact_source_pairs'] += 1

P = product(0.5, 6)
assert P < 0
rows = []
for sign in [-1, 1]:
    for j in range(2, 8):
        delta = sign * 10**(-j)
        ratio = source_derivative(0.5 + delta) / delta
        rows.append({'delta': delta, 'derivative_over_delta': ratio})
        if j == 7:
            assert abs(ratio + P / 3) < 2e-7
        counts['defect_ratios'] += 1

for j in range(1001):
    q = 0.49 + 0.02 * j / 1000
    Rq = 1 / (2 * (1 - q))
    lower = abs(source_derivative(q)) / (2 * math.pi * (1 + 12 * math.pi * Rq))
    upper = abs(q - 0.5) / 4
    # A comparison of analytic bounds, not computation of Delta_1.
    assert lower <= upper + 1e-16
    counts['bound_grid'] += 1

# ed. (2026-10-01): the receipt is also written by _ed_write (see above).
_ed_text = json.dumps({
    'status': 'PASS',
    'scope': 'Finite floating-point regressions; no interval or proof-assistant certification',
    'counts': counts,
    'total_regression_cases': sum(counts.values()),
    'tail_product_indices': {'start_inclusive': 2, 'stop_exclusive': 100},
    'P_truncated': P,
    'linear_lower_asymptotic_constant': abs(P) / (6 * math.pi * (1 + 12 * math.pi)),
    'global_adaptive_upper_constant': 0.25,
    'defect_ratio_rows': rows,
    'not_computed': ['optimal distance Delta_1', 'tangent-cone distances c_plus and c_minus',
                     'equality of one-sided coefficients'],
}, indent=2)
_ed_write('linear-verification.json', _ed_text + '\n')
print(_ed_text)
