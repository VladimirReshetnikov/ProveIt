#!/usr/bin/env python3
"""Exact certificates for the examples, using Python's standard library only.

Computes the quartic discriminant by an integer Sylvester determinant, counts
its real roots by Sturm's rule, and checks the height-two transform and the
binomial-normalized inequalities. No floating-point root solver is involved.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from math import comb
import json
from pathlib import Path
from support_tools import BipartiteGraph, ulc


def determinant_bareiss(matrix: list[list[int]]) -> int:
    """Fraction-free elimination, with row pivoting and checked exact divisions."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError('A square matrix is required.')
    if not n:
        return 1
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                value = a[i][j] * pivot - a[i][k] * a[k][j]
                quotient, remainder = divmod(value, previous)
                if remainder:
                    raise ArithmeticError('Bareiss division was not exact.')
                a[i][j] = quotient
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def sylvester(f: list[int], g: list[int]) -> list[list[int]]:
    """Sylvester matrix for descending coefficient lists."""
    m, n = len(f) - 1, len(g) - 1
    return ([([0] * k + f + [0] * (n - 1 - k)) for k in range(n)]
            + [([0] * k + g + [0] * (m - 1 - k)) for k in range(m)])


def trim(p: list[Fraction]) -> list[Fraction]:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def remainder(f: list[Fraction], g: list[Fraction]) -> list[Fraction]:
    """Polynomial remainder for ascending exact coefficient lists."""
    if all(x == 0 for x in g):
        raise ZeroDivisionError('Zero polynomial divisor.')
    r = trim(f[:])
    while any(r) and len(r) >= len(g):
        shift, factor = len(r) - len(g), r[-1] / g[-1]
        for j, coefficient in enumerate(g):
            r[j + shift] -= factor * coefficient
        trim(r)
    return r


def sturm_real_root_count(coefficients: list[int]) -> tuple[int, list[list[Fraction]]]:
    f = [Fraction(x) for x in coefficients]
    derivative = [k * f[k] for k in range(1, len(f))]
    seq = [f, derivative]
    while any(seq[-1]):
        r = [-x for x in remainder(seq[-2], seq[-1])]
        if not any(r):
            break
        seq.append(r)
    def variations(negative_infinity: bool) -> int:
        signs = []
        for p in seq:
            sign = 1 if p[-1] > 0 else -1
            if negative_infinity and (len(p) - 1) % 2:
                sign = -sign
            signs.append(sign)
        return sum(a != b for a, b in zip(signs, signs[1:]))
    return variations(True) - variations(False), seq


def certificate() -> dict:
    graph = BipartiteGraph((14, 3, 5, 9), 4)
    coefficients = [int(x) for x in graph.coefficients()]
    assert coefficients == [1, 9, 24, 16, 1]
    q = list(reversed(coefficients))
    dq = [q[k] * (4 - k) for k in range(4)]
    matrix = sylvester(q, dq)
    resultant = determinant_bareiss(matrix)
    discriminant = resultant  # monic quartic: (-1)^(4*3/2) = 1
    assert discriminant == -5243
    root_count, sturm_sequence = sturm_real_root_count(coefficients)
    assert root_count == 2

    n = graph.m + graph.n
    h = [0] * (n + 1)
    for k, c in enumerate(coefficients):
        for j in range(n - 2 * k + 1):
            h[k + j] += c * comb(n - 2 * k, j)
    assert h == [1, 17, 106, 303, 427, 303, 106, 17, 1]
    assert sum(h) == 1281 and ulc(h, n)
    normalized = [Fraction(c, comb(n, k)) for k, c in enumerate(h)]
    slack = [normalized[k] ** 2 - normalized[k - 1] * normalized[k + 1]
             for k in range(1, n)]
    assert all(x > 0 for x in slack)

    nontransitive = BipartiteGraph((3, 6, 4), 3)
    assert nontransitive.coefficients() == [1, 5, 6, 1]
    assert not nontransitive.palindromic_core_test()

    forest = BipartiteGraph((11, 4, 1), 4)
    forest_coefficients = forest.coefficients()
    assert forest_coefficients == [1, 5, 6, 2]
    double_norm = [c / (comb(3, k) * comb(4, k))
                   for k, c in enumerate(forest_coefficients)]
    assert double_norm[2] ** 2 < double_norm[1] * double_norm[3]

    return {
        'status': 'PASS',
        'arithmetic': 'exact integers and fractions; no external dependencies',
        'theta3_rows': list(graph.rows),
        'support_coefficients_ascending': coefficients,
        'sylvester_matrix': matrix,
        'resultant': resultant,
        'discriminant': discriminant,
        'distinct_real_roots_by_sturm': root_count,
        'sturm_sequence_ascending': [[str(x) for x in p] for p in sturm_sequence],
        'height_two_coefficients_ascending': h,
        'height_two_total': sum(h),
        'binomial_normalized': [str(x) for x in normalized],
        'normalized_log_concavity_slacks': [str(x) for x in slack],
        'nontransitive_example': [int(x) for x in nontransitive.coefficients()],
        'forest_double_normalized': [str(x) for x in double_norm],
        'scope': 'Exact finite certificates, not proofs of the all-graph theorems.'
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional output JSON path.')
    args = parser.parse_args()
    text = json.dumps(certificate(), indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')
