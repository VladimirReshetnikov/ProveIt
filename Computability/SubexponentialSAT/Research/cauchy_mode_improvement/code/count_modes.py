#!/usr/bin/env python3
"""Exact counts of abstract mode tuples at finite precision.

This is NOT a 3SAT solver or a SAT runtime benchmark.  For each scheme and
color count c, it computes the number of tuples of nonnegative integers
(beta[b,k]) satisfying sum_{b,k} weight(b)*beta[b,k] < precision.
The index b is unbounded here.  An actual packet additionally has a finite
rank cutoff; imposing that cutoff can only decrease these counts.

Run from any directory:
    python3 count_modes.py --output-dir ../results

Only Python's standard library is required.  All counts are exact integers;
logarithms and their ratios are floating-point descriptions of those integers.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from pathlib import Path
from typing import Callable

DEFAULT_PRECISIONS = (32, 64, 128, 256, 512, 1024, 2048, 4096)
DEFAULT_COLORS = (1, 4)


def factorial_valuation_two(b: int) -> int:
    """Legendre's identity, v_2(b!) = b - binary_digit_sum(b)."""
    if b < 0:
        raise ValueError('mode indices must be nonnegative')
    return b - b.bit_count()


def geometric_weight(b: int) -> int:
    return b + 1


def newton_weight(b: int) -> int:
    return b + 1 + factorial_valuation_two(b)


def skeleton_weight(b: int) -> int:
    return b + 1 + 2 * factorial_valuation_two(b)


WEIGHTS: dict[str, Callable[[int], int]] = {
    'geometric': geometric_weight,
    'newton': newton_weight,
    'skeleton': skeleton_weight,
}


def weight_list(scheme: str, cap: int) -> list[int]:
    """All weights strictly below cap; each sequence is increasing."""
    f = WEIGHTS[scheme]
    result = []
    b = 0
    while f(b) < cap:
        result.append(f(b))
        b += 1
    return result


def exact_coefficients(scheme: str, colors: int, cap: int) -> list[int]:
    """Coefficients through degree cap-1 of prod_b (1-x^weight(b))^-colors.

    The forward unbounded-coin update multiplies by (1-x^weight)^-1.
    Repeating it colors times keeps the colors distinct, as required for
    independent modes of equal weight.  Python integers retain exactness.
    """
    if cap < 1 or colors < 1:
        raise ValueError('cap and colors must both be positive')
    coefficients = [0] * cap
    coefficients[0] = 1
    for weight in weight_list(scheme, cap):
        for _ in range(colors):
            for degree in range(weight, cap):
                coefficients[degree] += coefficients[degree - weight]
    return coefficients


def enumerate_small(weights: list[int], budget: int, start: int = 0) -> int:
    """Independent recursive enumeration used only for small sanity checks."""
    if start == len(weights):
        return 1
    weight = weights[start]
    return sum(enumerate_small(weights, budget - e*weight, start+1)
               for e in range(budget // weight + 1))


def sanity_checks() -> dict[str, int]:
    # Ordinary partition numbers through degree seven.
    assert exact_coefficients('geometric', 1, 8) == [1, 1, 2, 3, 5, 7, 11, 15]
    checked = 0
    for scheme in WEIGHTS:
        for colors in (1, 2):
            for cap in range(1, 9):
                weights = [w for w in weight_list(scheme, cap)
                           for _ in range(colors)]
                exact = sum(exact_coefficients(scheme, colors, cap))
                independent = enumerate_small(weights, cap - 1)
                assert exact == independent, (scheme, colors, cap)
                checked += 1
    return {'recursive_enumeration_comparisons': checked,
            'ordinary_partition_reference_coefficients': 8}


def generate(precisions: tuple[int, ...], colors: tuple[int, ...]) -> dict:
    cap = max(precisions)
    check_result = sanity_checks()
    raw = {}
    for c in colors:
        for scheme in WEIGHTS:
            coefficients = exact_coefficients(scheme, c, cap)
            cumulative = 0
            requested = set(precisions)
            for degree, value in enumerate(coefficients):
                cumulative += value
                precision = degree + 1
                if precision in requested:
                    raw[c, scheme, precision] = cumulative
    rows = []
    for c in colors:
        for precision in precisions:
            base_log = math.log2(raw[c, 'geometric', precision])
            for scheme in WEIGHTS:
                count = raw[c, scheme, precision]
                log_count = math.log2(count)
                rows.append({'precision': precision, 'colors': c,
                             'scheme': scheme, 'count': str(count),
                             'log2_count': log_count,
                             'log2_ratio_to_geometric': log_count / base_log})
    return {
        'schema': 'mode-enumeration-counts-v1',
        'meaning': ('Exact abstract weighted mode-tuple counts, with strict '
                    'total weight below precision; not SAT running times.'),
        'finite_rank_cutoff': ('No finite tile-rank cutoff is imposed. '
                               'It can only reduce these counts.'),
        'arithmetic': 'Python arbitrary-precision integers; floats for logarithms only.',
        'precisions': list(precisions), 'color_counts': list(colors),
        'weights': {'geometric': 'b+1', 'newton': 'b+1+v2(b!)',
                    'skeleton': 'b+1+2*v2(b!)'},
        'predicted_limiting_log2_ratios': {'newton': 1/math.sqrt(2),
                                         'skeleton': 1/math.sqrt(3)},
        'sanity_checks': check_result, 'rows': rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path,
                        default=Path(__file__).resolve().parents[1]/'results')
    parser.add_argument('--precisions', nargs='+', type=int,
                        default=list(DEFAULT_PRECISIONS))
    parser.add_argument('--colors', nargs='+', type=int,
                        default=list(DEFAULT_COLORS))
    args = parser.parse_args()
    precisions = tuple(sorted(set(args.precisions)))
    colors = tuple(sorted(set(args.colors)))
    if min(precisions) < 2 or min(colors) < 1:
        parser.error('precisions must be >=2 and colors must be positive')
    result = generate(precisions, colors)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir/'mode_counts.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8')
    fields = list(result['rows'][0])
    with (args.output_dir/'mode_counts.csv').open('w', encoding='utf-8', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(result['rows'])
    print(json.dumps({'rows_written': len(result['rows']),
                      'maximum_precision': max(precisions),
                      'color_counts': list(colors),
                      'sanity_checks': result['sanity_checks'],
                      'output_dir': str(args.output_dir.resolve())}, indent=2))


if __name__ == '__main__':
    main()
