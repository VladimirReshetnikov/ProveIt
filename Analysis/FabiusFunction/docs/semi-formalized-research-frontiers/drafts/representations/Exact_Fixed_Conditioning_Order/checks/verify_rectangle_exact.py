#!/usr/bin/env python3
"""Exact rational regression checks. The manuscript gives the universal proof."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result beside itself, with CRLF on Windows). Pass
# --output-dir with this program's own directory, on a copy, to regenerate
# the recorded file.
def _ed_write(name, text):
    import argparse
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))


def positive_linear_integral(left, right):
    """Integral of the positive part of an affine function on a unit interval."""
    if left >= 0 and right >= 0:
        return F(left + right, 2)
    if left <= 0 and right <= 0:
        return F(0)
    if left > 0:
        return F(left * left, 2 * (left - right))
    return F(right * right, 2 * (right - left))


def chord_integral(values, shift):
    cumulative = [0]
    for value in values:
        cumulative.append(cumulative[-1] + value)
    return sum((positive_linear_integral(
        cumulative[i + shift] - cumulative[i],
        cumulative[i + shift + 1] - cumulative[i + 1])
        for i in range(len(values) - shift)), F(0))


def admissible(values):
    positive = [i for i, value in enumerate(values) if value > 0]
    return not positive or all(value >= 0 for value in values[positive[0]:positive[-1] + 1])


def main():
    profile_count = comparison_count = strict_count = 0
    for length in range(2, 9):
        for values in product((-1, 0, 1), repeat=length):
            if not admissible(values):
                continue
            profile_count += 1
            for b in range(1, length // 2 + 1):
                a = length - b
                lhs, rhs = chord_integral(values, b), chord_integral(values, a)
                assert lhs >= rhs, (values, a, b, lhs, rhs)
                comparison_count += 1
                strict_count += lhs > rhs
    level_count = 0
    for length in range(2, 17):
        for p in range(length + 1):
            for q in range(p, length + 1):
                for r in range(q, length + 1):
                    u, v = q - p, r - q
                    for b in range(1, length // 2 + 1):
                        a = length - b
                        def f(h):
                            overlap = max(0, min(q, r - h) - max(p, q - h))
                            formula = max(0, min(h, u, v, u + v - h))
                            assert overlap == formula
                            return overlap
                        assert f(b) >= f(a)
                        level_count += 1
    result = dict(status='passed', arithmetic='exact rational',
                  sign_profiles=profile_count, rectangle_comparisons=comparison_count,
                  strict_comparisons=strict_count, level_trapezoid_comparisons=level_count,
                  scope='Finite regression checks; the manuscript proves the universal statement.')
    # ed. (2026-10-01): written by _ed_write (see above).
    _ed_write('rectangle_exact.json', json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
