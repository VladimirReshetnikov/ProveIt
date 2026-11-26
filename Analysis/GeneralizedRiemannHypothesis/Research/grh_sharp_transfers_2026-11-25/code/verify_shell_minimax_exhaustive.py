#!/usr/bin/env python3
"""Independently exhaust all marked multisets for seven small p-adic shells.

Distances are represented by e_h*(v(z_a-z_b)-r_h) = p^v_p(a-b)-1.
No floating-point or p-adic library is used. The result checks the exact
maximin formula, not only the balanced construction.
"""
from itertools import combinations_with_replacement
import json


def ord_p(n, p):
    assert n
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def check(p, h):
    e = (p - 1) * p ** (h - 1)
    units = [a for a in range(1, p ** h) if a % p]
    distances = [[None if a == b else p ** ord_p(a - b, p) - 1
                  for b in units] for a in units]
    rows = []
    count = 0
    for m in range(e):
        claimed = sum((p - 1) * p ** (j - 1) * (m // ((p - 1) * p ** (j - 1)))
                      for j in range(1, h))
        best = -1
        multiset_count = 0
        for marks in combinations_with_replacement(range(e), m):
            unmarked = set(range(e)) - set(marks)
            minimum = min(sum(distances[a][b] for b in marks) for a in unmarked)
            best = max(best, minimum)
            multiset_count += 1
        assert best == claimed, (p, h, m, best, claimed)
        count += multiset_count
        rows.append({'m': m, 'max_min_scaled_excess': best,
                     'claimed_scaled_U': claimed, 'multisets': multiset_count})
    return {'p': p, 'h': h, 'e_h': e, 'multisets': count, 'cases': rows}


if __name__ == '__main__':
    cases = [check(p, h) for p, h in [(2, 1), (2, 2), (2, 3), (2, 4),
                                     (3, 1), (3, 2), (5, 1)]]
    print(json.dumps({'status': 'PASS',
                      'method': 'Exhaustive maximin over all marked multisets with m<e_h',
                      'shells': len(cases),
                      'budget_cases': sum(len(c['cases']) for c in cases),
                      'multisets': sum(c['multisets'] for c in cases),
                      'cases': cases}, indent=2))
