#!/usr/bin/env python3
"""Independent exact check of the finite-bound CSV.

This program deliberately does not import reversal.py. It obtains possible
permutation orders from an unrestricted composition recurrence, counts
surjections by inclusion-exclusion rather than Stirling recurrence, and
enumerates collision displacements rather than divisors.
Python 3.9+; standard library only.
"""
import csv
import json
from functools import lru_cache
from math import comb, factorial, gcd, lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


@lru_cache(None)
def bipartite(k, a, b):
    answer = 0
    for i in range(1, min(a, k) + 1):
        onto = sum((-1) ** (i-j) * comb(i, j) * j ** a for j in range(i+1))
        answer += comb(k, i) * onto * (k-i) ** b
    return answer


def main():
    with (ROOT / 'data/finite_range_bounds.csv').open(newline='') as f:
        rows = list(csv.DictReader(f))
    if not rows:
        raise ValueError('No finite-bound rows to verify.')
    maximum = max(int(row['n']) for row in rows)
    possible = [{1}]
    for r in range(1, maximum+1):
        possible.append({lcm(j, o) for j in range(1, r+1)
                         for o in possible[r-j]})

    @lru_cache(None)
    def tail_order(r, t):
        return max(lcm(t, o) for o in possible[r])

    checked = 0
    for row in rows:
        n, k = int(row['n']), int(row['k'])
        q, z = divmod(n, k)
        denominator = factorial(q) ** (k-z) * factorial(q+1) ** z
        gaps = [k**n - (k-1)**n, k**n-factorial(n)//denominator,
                (k-1)**2*k**(n-2)-1]
        for r in range(n-1):
            m = n-r
            for h in range(1, m):
                d = gcd(m, h)
                length = m//d
                chromatic = ((k-1)**length + (-1)**length*(k-1))**d*k**r
                gaps.append(chromatic-tail_order(r, m))
            for a in range(1, m//2+1):
                b = m-a
                d = gcd(a, b)
                chromatic = bipartite(k, a//d, b//d)**d*k**r
                period = (max(tail_order(r, a), tail_order(r, b))
                          if k == 3 and d == 1 else tail_order(r, lcm(a, b)))
                gaps.append(chromatic-period)
        upper = k**n-min(gaps)
        lower = max(k**n-bipartite(k, a, n-a)+(n-a if k == 3 else a*(n-a))
                    for a in range(2, (n+1)//2) if gcd(a, n-a) == 1)
        assert upper == int(row['upper']) and lower == int(row['lower'])
        assert upper == lower and int(row['match']) == 1
        checked += 1
    result = {'parameter_pairs_checked': checked, 'max_n': maximum,
              'all_upper_and_lower_values_reproduced': True,
              'imports_primary_implementation': False,
              'permutation_orders': 'Unrestricted composition recurrence',
              'chromatic_counts': 'Inclusion-exclusion for surjections',
              'same_cycle_parameters': 'All nonzero displacements'}
    (ROOT / 'data/independent_bounds_check.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
