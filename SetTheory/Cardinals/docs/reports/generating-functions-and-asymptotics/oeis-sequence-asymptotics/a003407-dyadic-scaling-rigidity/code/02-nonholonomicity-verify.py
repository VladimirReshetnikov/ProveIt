#!/usr/bin/env python3
"""Exact checks for the 3AP non-holonomicity article (Python >= 3.10).

The small counts are independently recomputed. The values at 64 and 75 are
published inputs: this script verifies the arithmetic separation, not their
enumeration. Numerical decimals are labelled diagnostic, never certificates.
No third-party packages or network access are required.
"""
from __future__ import annotations
import argparse
from decimal import Decimal, localcontext
from functools import lru_cache
from itertools import permutations
import json
from pathlib import Path
from time import perf_counter

EXPECTED = [1, 1, 2, 4, 10, 20, 48, 104, 282, 496, 1066, 2460, 6128,
            12840, 29380, 74904, 212728, 368016, 659296, 1371056,
            2937136, 6637232, 15616616, 38431556, 96547832, 198410168,
            419141312, 941812088, 2181990978, 5624657008, 14765405996,
            41918682488, 121728075232]
T64 = 39911512393313043466768
T75 = 30235147387260979648843264
ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    """Do not disable tests when Python is called with -O."""
    if not condition:
        raise AssertionError(message)


def count_three_free(n: int) -> tuple[int, int]:
    """Subset-state DP; see the article's proof of the midpoint transition."""
    if n < 0:
        raise ValueError('n must be nonnegative')
    full = (1 << n) - 1
    # Each test compares membership of the two possible endpoints around x.
    pairs = [tuple((1 << (x-d), 1 << (x+d))
                   for d in range(1, min(x, n-1-x)+1)) for x in range(n)]

    @lru_cache(maxsize=None)
    def continuations(used: int) -> int:
        if used == full:
            return 1
        remaining = full ^ used
        total = 0
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            x = bit.bit_length() - 1
            if all(bool(used & left) == bool(used & right)
                   for left, right in pairs[x]):
                total += continuations(used | bit)
        return total

    answer = continuations(0)
    return answer, continuations.cache_info().currsize


def brute_count(n: int) -> int:
    """Independent direct permutation enumeration, intentionally simple."""
    triples = [(i, j, k) for i in range(n) for j in range(i+1, n)
               for k in range(j+1, n)]
    return sum(all(p[i]+p[k] != 2*p[j] for i, j, k in triples)
               for p in permutations(range(1, n+1)))


def determinant_integer(a: list[list[int]]) -> int:
    """Fraction-free Bareiss elimination, with exact integer divisions."""
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError('determinant requires a square matrix')
    if n == 0:
        return 1
    a = [row[:] for row in a]
    sign, previous = 1, 1
    for k in range(n-1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = a[i][j]*pivot - a[i][k]*a[k][j]
                require(numerator % previous == 0, 'Bareiss division not exact')
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


def recurrence_matrix(counts: list[int], order: int, degree: int,
                      start: int = 0) -> list[list[int]]:
    size = (order+1)*(degree+1)
    if start+size-1+order >= len(counts):
        raise ValueError('not enough certified counts')
    return [[n**k*counts[n+j] for j in range(order+1)
             for k in range(degree+1)] for n in range(start, start+size)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=32,
                        help='independent DP bound, between 0 and 32')
    parser.add_argument('--brute-n', type=int, default=8,
                        help='direct permutation bound, between 0 and 8')
    parser.add_argument('--output', type=Path, default=ROOT/'data'/'verification.json')
    args = parser.parse_args()
    if not 0 <= args.max_n <= 32 or not 0 <= args.brute_n <= min(8, args.max_n):
        parser.error('require 0 <= brute-n <= min(8,max-n), 0 <= max-n <= 32')
    start_time = perf_counter()
    rows = []
    for n in range(args.max_n+1):
        value, states = count_three_free(n)
        require(value == EXPECTED[n], f'published count mismatch at {n}')
        if n <= args.brute_n:
            require(value == brute_count(n), f'brute-force mismatch at {n}')
        rows.append({'n': n, 'count': value, 'states': states})
    counts = [row['count'] for row in rows]
    for n in range(2, len(counts)):
        product = counts[n//2]*counts[(n+1)//2]
        require(2*product <= counts[n] <= 21*product, f'splitting bound at {n}')
    # Dyadic telescoping gives the strict logarithmic gap iff this integer > 0.
    lhs, rhs = (2*T64)**75, (21*T75)**64
    require(lhs > rhs, 'Ho separation failed')
    # A convenient positive rational lower bound for the logarithmic gap:
    # (2T64)^(1/64) > 2279/1000; (21T75)^(1/75) < 1139/500 = 2.278.
    require((2*T64)*1000**64 > 2279**64, 'lower rational root bracket')
    require((21*T75)*500**75 < 1139**75, 'upper rational root bracket')
    # log(2279/2278) > 1/2279, by log(1+x)>x/(1+x).
    # These deliberately wide bounds are enough to certify a nonzero gap.
    finite_certificates = []
    for order, degree, start in [(5, 3, 0), (4, 3, 8)]:
        size = (order+1)*(degree+1)
        if start+size-1+order < len(counts):
            det = determinant_integer(recurrence_matrix(counts, order, degree, start))
            require(det != 0, f'finite recurrence matrix singular: {order,degree,start}')
            finite_certificates.append({'order': order, 'degree': degree,
                                       'start': start, 'size': size,
                                       'determinant': str(det)})
    with localcontext() as ctx:
        ctx.prec = 70
        lower = Decimal(2*T64).ln()/64
        upper = Decimal(21*T75).ln()/75
        diagnostic = {'lower_log_rate': str(lower), 'upper_log_rate': str(upper),
                      'log_gap_lower_bound': str(lower-upper),
                      'lower_root_rate': str(lower.exp()),
                      'upper_root_rate': str(upper.exp())}
    record = {
        'status': 'all exact checks passed',
        'independent_enumeration_max_n': args.max_n,
        'direct_permutation_enumeration_max_n': args.brute_n,
        'counts': rows,
        'imported_large_counts': {'64': T64, '75': T75,
             'source': 'B. S. Ho, arXiv:2602.13617v1; Correll-Ho/OEIS table',
             'independently_recomputed_here': False},
        'separation': {'left': str(lhs), 'right': str(rhs),
                       'difference': str(lhs-rhs), 'strict': lhs > rhs,
                       'certified_root_bounds': ['lower > 2279/1000',
                                                  'upper < 1139/500'],
                       'certified_log_gap': '> 1/2279'},
        'finite_recurrence_certificates': finite_certificates,
        'diagnostic_decimals_not_used_as_proof': diagnostic,
        'runtime_seconds': round(perf_counter()-start_time, 6),
        'limits': ['not a Lean or Rocq proof',
                   'does not prove infinite splitting bounds',
                   'does not re-enumerate theta(64) or theta(75)',
                   'finite determinant checks do not prove non-P-recursiveness']
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: record[k] for k in ['status', 'independent_enumeration_max_n',
                                           'direct_permutation_enumeration_max_n',
                                           'runtime_seconds']}, indent=2))
    print('Finite determinant certificates:', [(x['order'],x['degree'],x['start'])
                                                for x in finite_certificates])
    print('Diagnostic logarithmic separation:', diagnostic['log_gap_lower_bound'])
    print('Full record:', args.output)


if __name__ == '__main__':
    main()
