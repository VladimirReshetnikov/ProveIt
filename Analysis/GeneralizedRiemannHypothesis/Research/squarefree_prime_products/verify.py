#!/usr/bin/env python3
"""Exact finite tests for the distribution of products of distinct primes.

Usage: python3 verify.py
Outputs deterministic JSON to stdout. All arithmetic is integral.
"""
from collections import Counter
from itertools import combinations
from math import comb, gcd, isqrt, prod
import json


def units(q):
    return [a for a in range(1, q) if gcd(a, q) == 1]


def primes_to(x, q):
    return [p for p in range(2, x + 1)
            if gcd(p, q) == 1 and all(p % d for d in range(2, isqrt(p) + 1))]


def direct_counts(primes, q, k):
    counts = dict.fromkeys(units(q), 0)
    for chosen in combinations(primes, k):
        counts[prod(chosen) % q] += 1
    return counts


def group_algebra_counts(primes, q, k):
    """Coefficients of prod_p (1 + t[p mod q]) in Z[(Z/qZ)^*][t]."""
    residues = units(q)
    levels = [dict.fromkeys(residues, 0) for _ in range(k + 1)]
    levels[0][1] = 1
    for p in primes:
        for j in range(k, 0, -1):
            for a, previous in levels[j - 1].items():
                levels[j][p * a % q] += previous
    return levels[k]


def verified_counts(primes, q, k):
    first = direct_counts(primes, q, k)
    second = group_algebra_counts(primes, q, k)
    if first != second or sum(first.values()) != comb(len(primes), k):
        raise ArithmeticError("Inconsistent representation counts")
    return first


def exhaustive(q, x, k, sizes):
    source = primes_to(x, q)
    experiments = []
    for m in sizes:
        minima = Counter()
        worst = None
        for retained in combinations(source, m):
            counts = verified_counts(retained, q, k)
            low = min(counts.values())
            minima[low] += 1
            if worst is None or low < worst['minimum']:
                worst = {'minimum': low, 'retained': retained,
                         'counts_by_residue': counts}
        if sum(minima.values()) != comb(len(source), m):
            raise ArithmeticError("Incomplete retained-set enumeration")
        experiments.append({'m': m, 'number_of_sets': sum(minima.values()),
                            'histogram_of_minimum': dict(sorted(minima.items())),
                            'worst_witness': worst})
    return {'q': q, 'x': x, 'k': k, 'eligible_primes': source,
            'experiments': experiments}


def quadratic(q, x, sign_modulus, extra, k):
    """Retain all PLUS primes, then the first extra MINUS primes."""
    source = primes_to(x, q)
    squares = {pow(a, 2, sign_modulus) for a in units(sign_modulus)}
    sign = {a: (1 if a % sign_modulus in squares else -1) for a in units(q)}
    for a in sign:
        for b in sign:
            if sign[a*b % q] != sign[a] * sign[b]:
                raise ArithmeticError("Quadratic character is not multiplicative")
    plus = [p for p in source if sign[p % q] == 1]
    minus = [p for p in source if sign[p % q] == -1]
    if not (0 <= extra <= len(minus) and k <= len(plus)):
        raise ValueError("Invalid example parameters")
    retained = plus + minus[:extra]
    counts = verified_counts(retained, q, k)
    total = comb(len(retained), k)
    observed = sum(sign[a] * counts[a] for a in sign)
    expected = sum((-1)**i * comb(extra, i) * comb(len(plus), k-i)
                   for i in range(min(extra, k) + 1))
    if observed != expected or (not extra and observed != total):
        raise ArithmeticError("Quadratic projection identity failed")
    return {'q': q, 'x': x, 'sign_modulus': sign_modulus, 'k': k,
            'source_size': len(source), 'plus_available': len(plus),
            'minus_available': len(minus), 'minus_retained': extra,
            'retained_size': len(retained), 'retained': sorted(retained),
            'quadratic_sign_by_residue': sign, 'counts_by_residue': counts,
            'positive_products': (total + observed)//2,
            'negative_products': (total - observed)//2,
            'signed_projection': observed, 'total_products': total}


def cubic_obstruction():
    """Use a cubic quotient modulo 13 and keep one prime outside its kernel."""
    q, x, k = 13, 211, 5
    source = primes_to(x, q)
    quotient = {pow(2, j, q): j % 3 for j in range(q - 1)}
    kernel = [p for p in source if quotient[p % q] == 0]
    outlier = next(p for p in source if quotient[p % q] == 1)
    retained = sorted(kernel + [outlier])
    counts = verified_counts(retained, q, k)
    fibers = [sum(n for a, n in counts.items() if quotient[a] == v)
              for v in range(3)]
    predicted = [comb(len(kernel), k), comb(len(kernel), k - 1), 0]
    observed_support = {a for a, n in counts.items() if n}
    full_fibers = {a for a in units(q) if quotient[a] in (0, 1)}
    signs = {pow(p, (q - 1) // 2, q) for p in retained}
    if fibers != predicted or observed_support != full_fibers or signs != {1, 12}:
        raise ArithmeticError("Cubic example failed")
    return {'q': q, 'x': x, 'k': k, 'source_size': len(source),
            'kernel_primes': kernel, 'outlier': outlier, 'counts_by_residue': counts,
            'counts_by_cubic_class': fibers, 'classes_reached': len(observed_support)}


def main():
    data = {
        'cubic_test': cubic_obstruction(),
        'exhaustive_tests': [exhaustive(7, 47, 3, [7, 8, 9]),
                             exhaustive(15, 37, 3, [5, 6, 7])],
        'quadratic_tests': [quadratic(7, 47, 7, 0, 3),
                            quadratic(7, 47, 7, 3, 3),
                            quadratic(15, 37, 3, 0, 3),
                            quadratic(15, 37, 3, 2, 3),
                            quadratic(13, 211, 13, 3, 3)],
    }
    print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
