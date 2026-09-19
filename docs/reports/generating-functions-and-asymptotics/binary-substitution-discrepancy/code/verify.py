#!/usr/bin/env python3
"""Reproduce the exact checks and research data.

Run `python code/verify.py --long` from the package root. No third-party
packages are needed. The optional long test literally builds 20,222,898
letters; the default suite instead uses small words and exact block summaries.
Outputs are written to data/; all theorem inequalities use exact integers.
"""
from __future__ import annotations

import argparse
import json
import platform
import random
from decimal import Decimal, localcontext
from pathlib import Path
from time import perf_counter

from substitution import (Quad, Substitution, concatenate, direct_prefix,
                          empty_summary, extremal_family, letter_summary)
from independent_check import verify as independent_verify

ROOT = Path(__file__).resolve().parent.parent


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--long', action='store_true', help='also build a 20-million-letter prefix')
    args = parser.parse_args()
    started = perf_counter()
    totals: dict[str, int] = {}

    def check(condition: bool, group: str) -> None:
        if not condition:
            raise AssertionError(f'Failed check in {group}')
        totals[group] = totals.get(group, 0) + 1

    rng = random.Random(284366)
    for m in range(1, 9):
        q = Quad(m, 0, 1)
        check(q*q == m*(1-q), 'quadratic_arithmetic')
        check(q.sign() > 0 and (1-q).sign() > 0, 'quadratic_arithmetic')
        for _ in range(300):
            a, b = rng.randrange(-10**8, 10**8), rng.randrange(-10**8, 10**8)
            x = Quad(m, a, b)
            numerical = x.decimal(80)
            check(x.sign() == ((numerical > 0)-(numerical < 0)), 'quadratic_arithmetic')
        model = Substitution(m)
        word = direct_prefix(m, 12000)
        z = o = 0
        den = 1-q*q
        # All positions in a literal prefix, independently counted.
        for p, c in enumerate(word, 1):
            if c == '1':
                o += 1
                e = Quad(m, o-p, o)
                check((e*den-q).sign() < 0, 'sharp_bounds')
                check(((e+m)*den-q).sign() > 0, 'sharp_bounds')
                if p % 17 == 0 or p < 200:
                    check(model.select(1, o) == p, 'random_access')
            else:
                z += 1
                qe = Quad(m, z, z-p)
                check((qe*den-q*q).sign() < 0, 'sharp_bounds')
                check(((qe-1)*den+q).sign() > 0, 'sharp_bounds')
                if p % 17 == 0 or p < 200:
                    check(model.select(0, z) == p, 'random_access')
            x = Quad(m, z, -o)
            check((x*den+q).sign() > 0 and (q*q-x*den).sign() > 0,
                  'prefix_bounds')
            if p % 19 == 0 or p < 200:
                check(model.prefix_counts(p) == (z, o), 'random_access')
        check(model.prefix_counts(0) == (0, 0), 'random_access')
        # Direct concatenation of individual letters versus recursive block summaries.
        for k in range(7):
            block = model.block(k)
            if block.length > 12000:
                break
            literal = empty_summary(m)
            for c in word[:block.length]:
                literal = concatenate(literal, letter_summary(m, int(c)))
            check(literal == block, 'block_extrema')
        for n in range(1, 151):
            v = model.select(1, n)
            for h in range(1, m+1):
                u = model.select(0, m*(n-1)+h)
                check(u == v+(2*m-1)*n-2*m+2*h, 'position_transfer')
        # Exact extremal family, including random access at very large indices.
        family = extremal_family(m, 25)
        power = q*q
        for j, row in enumerate(family):
            n, p = row['rank'], row['position']
            e = Quad(m, n-p, n)
            check(model.select(1, n) == p, 'extremal_family')
            check(e*den == q*(1-power), 'extremal_family')
            power = power*q*q
            if j >= 2:
                T, D = m*(m+2), m*m
                check(n == T*family[j-1]['rank']-D*family[j-2]['rank']+1-m,
                      'family_recurrences')
                check(p == T*family[j-1]['position']-D*family[j-2]['position']+m*m-m+1,
                      'family_recurrences')
        # Multiply the proposed generating functions by their denominator.
        denominator = [1, -(m*(m+2)+1), m*m+m*(m+2), -m*m]
        for field, numerator in [('rank', [1, -m]), ('position', [1, m*(m-1)])]:
            for j in range(len(family)):
                coefficient = sum(denominator[h]*family[j-h][field]
                                  for h in range(min(3, j)+1))
                check(coefficient == (numerator[j] if j < 2 else 0),
                      'family_generating_functions')

    model = Substitution(3)
    # Displayed initial terms transcribed from the three OEIS entries, accessed
    # 2026-09-19. This is not a claim to have checked the entire linked b-files.
    zeros = [2,4,6,9,11,13,16,18,20,23,25,27,29,31,33,36,38,40,43,45,47,50,52,54,56,58,60,63,65,67]
    ones = [1,3,5,7,8,10,12,14,15,17,19,21,22,24,26,28,30,32,34,35,37,39,41,42,44,46,48,49,51,53]
    bits = [1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1]
    for symbol, values in [(0, zeros), (1, ones)]:
        for rank, p in enumerate(values, 1):
            check(model.select(symbol, rank) == p, 'oeis_initial_terms')
    check([int(c) for c in direct_prefix(3, len(bits))] == bits, 'oeis_initial_terms')

    first_one = model.first_at_least(1)
    first_zero = model.first_at_least(0)
    check((first_one['rank'], first_one['position']) == (2977771, 5334043), 'first_counterexamples')
    check((first_zero['rank'], first_zero['position']) == (8933313, 20222898), 'first_counterexamples')
    check(model.first_at_least(1, max_level=11) is None, 'first_counterexamples')
    check(model.first_at_least(0, max_level=12) is None, 'first_counterexamples')
    independent = independent_verify()
    check(independent['first_one_rank'] == first_one['rank'], 'independent_certificate')

    p_summary = empty_summary(3)
    for k in [11, 10, 10, 8, 6, 4, 2]:
        p_summary = concatenate(p_summary, model.block(k))
    check(p_summary.length == 5334042, 'prefix_certificate')
    check(p_summary.minimum[1].value == Quad(3, 431712, -545583), 'prefix_certificate')
    check(p_summary.minimum[1].position == 977295, 'prefix_certificate')

    long_result = None
    if args.long:
        word = direct_prefix(3, 20222898)
        z, o = word[:5334042].count('0'), word[:5334042].count('1')
        check((z, o, word[5334042]) == (2356272, 2977770, '1'), 'long_literal_prefix')
        check(word[-1] == '0' and word.count('0') == 8933313, 'long_literal_prefix')
        check(word.count('1') == 11289585, 'long_literal_prefix')
        long_result = {'length': len(word), 'zeros': word.count('0'), 'ones': word.count('1')}

    block_rows = []
    q = Quad(3, 0, 1)
    for k in range(31):
        b = model.block(k)
        e_min, e_max = q-b.maximum[1].value, q-b.minimum[1].value
        block_rows.append({'k': k, 'length': b.length, 'zeros': b.zeros, 'ones': b.ones,
                           'min_prefix_before_one': b.minimum[1].value.as_dict(),
                           'min_error_one': e_min.as_dict(), 'max_error_one': e_max.as_dict(),
                           'min_error_one_decimal': str(e_min.decimal()),
                           'max_error_one_decimal': str(e_max.decimal())})
    certificate = {'first_one': first_one, 'first_zero': first_zero,
                   'prefix_block_levels': [11,10,10,8,6,4,2],
                   'prefix_length': p_summary.length, 'prefix_zeros': p_summary.zeros,
                   'prefix_ones': p_summary.ones,
                   'minimum_weight_before_one': p_summary.minimum[1].value.as_dict(),
                   'earlier_maximum_error': Quad(3, -431712, 545584).as_dict(),
                   'counterexample_error': Quad(3, -2356272, 2977771).as_dict(),
                   'integer_square_differences': {'earlier_safe': 110224, 'one_violation': 265940,
                                                  'zero_violation': 2393460}}
    report = {'status': 'PASS', 'python': platform.python_version(),
              'elapsed_seconds': round(perf_counter()-started, 3),
              'assertions_by_group': totals, 'total_assertions': sum(totals.values()),
              'independent_certificate': independent, 'literal_large_prefix': long_result,
              'precision_policy': 'All inequalities exact; Decimal is only a display or cross-check.'}
    data = ROOT / 'data'
    data.mkdir(exist_ok=True)
    for name, obj in [('verification', report), ('certificates', certificate),
                      ('extremal_family', extremal_family(3, 25)), ('finite_extrema', block_rows)]:
        (data / f'{name}.json').write_text(json.dumps(obj, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
