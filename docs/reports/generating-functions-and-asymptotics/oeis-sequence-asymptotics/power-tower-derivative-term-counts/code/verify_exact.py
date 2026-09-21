#!/usr/bin/env python3
"""Exact A290268 checks, with three independent coefficient formulas.
Python 3.10+, standard library only. The bound is finite, not a global proof.
"""
from __future__ import annotations

import argparse
import csv
import json
from collections import defaultdict
from fractions import Fraction
from math import comb, factorial
from pathlib import Path


def upper_bound(n: int) -> int:
    return ((n * n + 2 * n + 2) // 2 if n % 2 == 0
            else (n * n + 2 * n + 1) // 2 - (n + 1) // 8)


def forced_zero(n: int, k: int, j: int) -> bool:
    return ((j == k and n > 2 * k)
            or (k % 2 == 0 and n == 4 * k - 2 * j + 1))


def next_row(n: int, row: dict[tuple[int, int], int]) -> dict[tuple[int, int], int]:
    result: dict[tuple[int, int], int] = defaultdict(int)
    for (k, j), value in row.items():
        result[k, j] += (2 * k - n) * value
        if j:
            result[k, j - 1] += j * value
        result[k + 1, j] += value
        result[k + 1, j + 1] += 2 * value
    return {index: value for index, value in result.items() if value != 0}


def multiply(a: list[Fraction], b: list[Fraction], limit: int) -> list[Fraction]:
    result = [Fraction(0)] * (limit + 1)
    for i, x in enumerate(a[:limit + 1]):
        if not x:
            continue
        for j, y in enumerate(b[:limit - i + 1]):
            if y:
                result[i + j] += x * y
    return result


def powers(a: list[Fraction], limit: int) -> list[list[Fraction]]:
    result = [[Fraction(1)] + [Fraction(0)] * limit]
    for _ in range(limit):
        result.append(multiply(result[-1], a, limit))
    return result


def shifted_falling_coefficient(n: int, shift: int, degree: int) -> int:
    """[v^degree] product(v+shift-r, r=0,...,n-1)."""
    coeff = [1] + [0] * degree
    for r in range(n):
        for h in range(degree, -1, -1):
            coeff[h] = (shift - r) * coeff[h] + (coeff[h - 1] if h else 0)
    return coeff[degree]


def difference_formula(n: int, k: int, j: int) -> Fraction:
    m = k - j
    total = sum((-1) ** (j - h) * comb(j, h)
                * shifted_falling_coefficient(n, 2 * m + 2 * h, m)
                for h in range(j + 1))
    return Fraction(total, factorial(j))


def integer_binomial(n: int, k: int) -> int:
    result = 1
    for i in range(1, k + 1):
        result = result * (n - i + 1) // i
    return result


def independent_checks(rows: list[dict[tuple[int, int], int]], limit: int) -> int:
    a = [Fraction(0)] * (limit + 1)
    if limit >= 1: a[1] = Fraction(2)
    if limit >= 2: a[2] = Fraction(1)
    b = [Fraction(0)] * (limit + 1)
    if limit >= 1: b[1] = Fraction(1)
    if limit >= 2: b[2] = Fraction(3, 2)
    for n in range(3, limit + 1):
        b[n] = Fraction(2 * (-1) ** (n - 3), n * (n - 1) * (n - 2))
    h = [Fraction(1, n + 1) if n % 2 == 0 else Fraction(0)
         for n in range(limit + 1)]
    ap, bp, hp = powers(a, limit), powers(b, limit), powers(h, limit)
    count = 0
    for n in range(limit + 1):
        for k in range(n + 1):
            for j in range(k + 1):
                m, r, d = k - j, n - k, n - 2 * k - 1
                actual = rows[n].get((k, j), 0)
                egf = (Fraction(factorial(n), factorial(j) * factorial(m))
                       * sum(ap[j][s] * bp[m][n - s] for s in range(n + 1)))
                diff = difference_formula(n, k, j)
                left = [Fraction((-1) ** s * integer_binomial(d, s))
                        for s in range(r + 1)]
                right = [Fraction(comb(2 * m, s)) if s <= 2 * m else Fraction(0)
                         for s in range(r + 1)]
                mobius = (Fraction(factorial(n), factorial(j) * factorial(m))
                          * Fraction(2) ** (2 * j + m - n)
                          * multiply(multiply(left, right, r), hp[m], r)[r])
                assert egf == diff == mobius == actual, (n, k, j, actual, egf, diff, mobius)
                count += 1
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=200)
    parser.add_argument('--formula-n', type=int, default=16)
    parser.add_argument('--output-dir', type=Path, default=Path('data'))
    args = parser.parse_args()
    if not 0 <= args.formula_n <= args.max_n:
        parser.error('Require 0 <= formula-n <= max-n.')
    args.output_dir.mkdir(parents=True, exist_ok=True)
    row = {(0, 0): 1}
    small_rows = []
    counts = []
    examined = 0
    for n in range(args.max_n + 1):
        if n <= args.formula_n:
            small_rows.append(row.copy())
        assert len(row) == upper_bound(n), (n, len(row), upper_bound(n))
        for k in range(1, n + 1):
            for j in range(k + 1):
                value = row.get((k, j), 0)
                assert (value == 0) == forced_zero(n, k, j), (n, k, j)
                if n <= 2 * k or (n == 2 * k + 1 and j < k):
                    assert value > 0, (n, k, j, 'positivity')
                m, d = k - j, n - 2 * k - 1
                if n > 2 * k and m in (1, 2):
                    factor = 1
                    if m == 1 and j % 2 == 1: factor = 2 - d
                    if m == 2 and j % 2 == 0: factor = 4 - d
                    predicted_sign = (-1) ** (n - 1) * ((factor > 0) - (factor < 0))
                    assert ((value > 0) - (value < 0)) == predicted_sign
                examined += 1
        counts.append((n, len(row), upper_bound(n)))
        if n < args.max_n:
            row = next_row(n, row)
    cross_checks = independent_checks(small_rows, args.formula_n)
    # Counterexample to an overbroad nonvanishing assertion about falling factorials.
    assert shifted_falling_coefficient(8, 2, 5) == 0
    assert shifted_falling_coefficient(8, 5, 5) == 0
    with (args.output_dir / 'exact_counts.csv').open('w', newline='') as out:
        writer = csv.writer(out)
        writer.writerow(['n', 'exact_nonzero_coefficients', 'upper_bound'])
        writer.writerows(counts)
    examples = {str(n): {f'{k},{j}': v for (k, j), v in sorted(small_rows[n].items())}
                for n in (0, 1, 2, 3, 7, 9) if n <= args.formula_n}
    (args.output_dir / 'sample_coefficients.json').write_text(json.dumps(examples, indent=2) + '\n')
    report = {'exact_support_max_n': args.max_n,
              'examined_triangle_cells': examined,
              'independent_formulas_max_n': args.formula_n,
              'coefficient_triples_cross_checked': cross_checks,
              'independent_formulas': ['generating_function', 'finite_difference', 'mobius'],
              'support_pattern': 'PASS', 'positivity': 'PASS',
              'first_two_log_deficits_signs': 'PASS',
              'global_conjecture_status': 'NOT PROVED by this finite computation'}
    (args.output_dir / 'exact_summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
