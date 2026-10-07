#!/usr/bin/env python3
"""Exact checks of the prime-cyclic punctured-sign cube polynomials.

Subset-sum state counting is checked against the defining Gowers derivative
recursion, using integer arithmetic. This finite verification supplements the
uniform argument in the article; it is not a substitute for that proof.
"""

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def rotate(mask, h, p):
    all_bits = (1 << p) - 1
    return ((mask << h) | (mask >> (p - h))) & all_bits


def subset_coefficients(p):
    states = {1: 1}
    coeff = []
    for j in range(p - 1):
        coeff.append(sum(count * (p - mask.bit_count())
                         for mask, count in states.items()))
        require(sum(states.values()) == (p - 1) ** j,
                f'subset-state multiplicities disagree for p={p}, j={j}')
        next_states = defaultdict(int)
        for mask, count in states.items():
            for h in range(1, p):
                next_states[mask | rotate(mask, h, p)] += count
        states = next_states
    require(states == {(1 << p) - 1: (p - 1) ** (p - 1)},
            f'nonzero directions failed to cover the group for p={p}')
    return coeff


@lru_cache(maxsize=None)
def cube_sum(values, d):
    """Unnormalized sum over x,h1,...,hd, computed by derivative recursion."""
    if d == 1:
        return sum(values) ** 2
    p = len(values)
    return sum(cube_sum(tuple(values[x] * values[(x + h) % p]
                               for x in range(p)), d - 1)
               for h in range(p))


def verify_case(p):
    coeff = subset_coefficients(p)
    require(coeff[0] == p - 1, 'constant coefficient failed')
    expected_top = (p - 1) * 2 ** (p - 3)
    require(coeff[-1] == expected_top, 'leading coefficient failed')
    balanced = tuple([0] + [1] * ((p - 1) // 2) + [-1] * ((p - 1) // 2))
    positive = tuple([0] + [1] * (p - 1))
    one_negative = tuple([0, -1] + [1] * (p - 2))
    tests = []
    # Independent Gowers recursion for several orders and sign assignments.
    if p <= 7:
        for d in range(max(2, p - 1), p + 3):
            predicted = sum(comb(d, j) * a for j, a in enumerate(coeff))
            for name, values in [('balanced', balanced), ('positive', positive),
                                 ('one_negative', one_negative)]:
                observed = cube_sum(values, d)
                require(observed == predicted,
                        f'cube identity failed for p={p}, d={d}, f={name}')
            tests.append({'d': d, 'cube_sum': predicted,
                          'Q_d': str(Fraction(predicted, p ** (d + 1)))})
        d = p - 2
        require(cube_sum(one_negative, d) < cube_sum(positive, d),
                'claimed sharp dimension threshold not witnessed')
    return {
        'p': p,
        'binomial_coefficients_A_p_j': coeff,
        'leading_monomial_coefficient': str(Fraction(expected_top, factorial(p - 2))),
        'tests': tests,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases = [verify_case(p) for p in (3, 5, 7, 11, 13)]
    report = {
        'status': 'all exact checks passed',
        'arithmetic': 'integers and fractions only',
        'methods': ['subset-sum state dynamic programming',
                    'independent multiplicative-derivative recursion'],
        'cases': cases,
    }
    result = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(result, encoding='utf-8')
    print(result)


if __name__ == '__main__':
    main()
