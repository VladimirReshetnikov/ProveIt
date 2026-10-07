#!/usr/bin/env python3
"""Exact verification of a degree-16 observation on twenty unbiased bits.

Only Python's standard library is used. Blocks of four bits are compressed
by their number of +1 signs; the multiplicity is binomial(4,j). All 5**5
compressed configurations are enumerated, accounting for all 2**20 inputs.
The analytic cell-degree proof is in the accompanying note; enumeration
checks retained variance and all conditional moments independently.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import comb
import json


def canonical_report(n, fallback, indices):
    """Indices 0..n encode H_n=2j-n; leaves have target indices 1..n."""
    center = indices[0]
    leaves = indices[1:]
    selected = center + 1 if center < n else fallback  # 1-based leaf
    all_pass = all(j == target for target, j in enumerate(leaves, 1))
    others_pass = all(j == target for target, j in enumerate(leaves, 1)
                      if target != selected)
    if all_pass:
        return ('B',)
    if others_pass:
        return ('A',)
    return ('ordinary', center, selected,
            tuple(j for target, j in enumerate(leaves, 1) if target != selected))


def enumerate_reporter(n=4, fallback=3):
    cells = defaultdict(lambda: [0, 0, 0])
    special_leaf_character_numerator = 0
    for indices in product(range(n + 1), repeat=n + 1):
        multiplicity = 1
        for j in indices:
            multiplicity *= comb(n, j)
        total = sum(2 * j - n for j in indices)
        report = canonical_report(n, fallback, indices)
        statistics = cells[report]
        statistics[0] += multiplicity
        statistics[1] += multiplicity * total
        statistics[2] += multiplicity * total * total
        if report == ('A',):
            # On a block with j positive signs, the full-block character
            # equals (-1)**(n-j). No polynomial decomposition is used here.
            leaf_character = (-1) ** sum(n - j for j in indices[1:])
            special_leaf_character_numerator += multiplicity * leaf_character
    denominator = 2 ** (n * (n + 1))
    assert sum(s[0] for s in cells.values()) == denominator
    assert sum(s[1] for s in cells.values()) == 0
    assert sum(s[2] for s in cells.values()) == n * (n + 1) * denominator
    variance = sum((Fraction(s[1] ** 2, s[0] * denominator)
                    for s in cells.values()), Fraction())
    special_leaf_character = Fraction(special_leaf_character_numerator, denominator)
    special = {}
    for label in ('A', 'B'):
        count, first, second = cells[(label,)]
        mean = Fraction(first, count)
        conditional_variance = Fraction(second, count) - mean * mean
        special[label] = {
            'count': count,
            'probability': str(Fraction(count, denominator)),
            'mean': str(mean),
            'variance': str(conditional_variance),
        }
    ordinary_variances = set()
    for label, (count, first, second) in cells.items():
        if label[0] == 'ordinary':
            ordinary_variances.add(Fraction(second, count) - Fraction(first, count) ** 2)
    assert ordinary_variances == {Fraction(n)}
    score_values = {Fraction(first, count) for count, first, second in cells.values()}
    if (n, fallback) == (4, 3):
        assert variance == Fraction(16) + Fraction(9, 34816)
        assert special['A']['probability'] == '17/2048'
        assert special['A']['mean'] == '31/17'
        assert special['A']['variance'] == '1147/289'
        assert score_values == {Fraction(k) for k in range(-16, 17, 2)} | {Fraction(31, 17)}
        assert special_leaf_character == Fraction(-3, 2048)
    return {
        'bits': n * (n + 1),
        'block_bits': n,
        'cell_degree': n * n,
        'fallback': fallback,
        'compressed_states': (n + 1) ** (n + 1),
        'number_of_reports': len(cells),
        'number_of_score_values': len(score_values),
        'score_values': [str(s) for s in sorted(score_values)],
        'retained_variance': str(variance),
        'variance_surplus': str(variance - n * n),
        'A_full_leaf_character_coefficient': str(special_leaf_character),
        'special_cells': special,
    }


def analytic_reporter(n, fallback):
    """Closed exact formula, not used in enumerate_reporter."""
    pstar = Fraction(1)
    for j in range(1, n + 1):
        pstar *= Fraction(comb(n, j), 2 ** n)
    harmonic = sum((Fraction(1, j) for j in range(1, n + 1)), Fraction())
    choose = comb(n, fallback)
    a = n + 1 - fallback
    w = (n + 1) * (harmonic - 1) + Fraction(1, choose)
    u = Fraction(a, choose) - 1
    surplus = 4 * pstar * (1 - Fraction(a * a, choose) + u * u / w)
    return Fraction(n * n) + surplus


if __name__ == '__main__':
    report = enumerate_reporter()
    assert Fraction(report['retained_variance']) == analytic_reporter(4, 3)
    for n in (2, 3, 4, 5):
        for fallback in range(1, n + 1):
            exact = enumerate_reporter(n, fallback)
            assert Fraction(exact['retained_variance']) == analytic_reporter(n, fallback)
    print(json.dumps(report, indent=2))
