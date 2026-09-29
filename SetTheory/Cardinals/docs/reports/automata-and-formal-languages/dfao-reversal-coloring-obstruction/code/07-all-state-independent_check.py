#!/usr/bin/env python3
"""Independent finite checker; imports no code from verify.py.

Uses Stirling-number color counts, a path-count recurrence for cycles,
descending integer partitions, and a base-4 integer BFS. This is
implementation independence, not independence of the mathematical method.
"""
from __future__ import annotations
import json
from array import array
from functools import lru_cache
from math import comb, factorial, gcd, lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def check(ok: bool, reason: str) -> None:
    if not ok:
        raise AssertionError(reason)


@lru_cache(None)
def partitions(total: int, largest: int) -> tuple[tuple[int, ...], ...]:
    if total == 0:
        return ((),)
    return tuple((head,) + tail
                 for head in range(min(total, largest), 0, -1)
                 for tail in partitions(total-head, head))


@lru_cache(None)
def maximum_order(t: int, residual: int) -> int:
    return max(lcm(t, *p) for p in partitions(residual, residual))


@lru_cache(None)
def stirling(n: int, j: int) -> int:
    if n == 0:
        return int(j == 0)
    if j <= 0 or j > n:
        return 0
    return stirling(n-1, j-1) + j*stirling(n-1, j)


@lru_cache(None)
def proper_biclique(a: int, b: int) -> int:
    return sum(comb(4,j)*factorial(j)*stirling(a,j)*(4-j)**b
               for j in range(1, min(3,a)+1))


def proper_cycle(length: int) -> int:
    same, different = 1, 0
    for _ in range(1, length):
        same, different = different, 3*same + 2*different
    return 4*different


def canonical(row: dict) -> tuple:
    return row['kind'], tuple(row['parameters']), row['deficit']


def check_finite() -> int:
    loaded = json.loads((ROOT/'data/finite_certificate.json').read_text())
    check([item['n'] for item in loaded] == list(range(4,26)), 'Missing size')
    count = 0
    for entry in loaded:
        n = entry['n']
        expected = [('permutations', (), 3*4**(n-1)),
                    ('singulars', (), 9*4**(n-2)-1)]
        for r in range(n-1):
            m = n-r
            for length in range(2, m+1):
                if m % length == 0:
                    d = m//length
                    val = proper_cycle(length)**d*4**r - maximum_order(m,r)
                    expected.append(('same', (m,d,r), val))
            for a in range(1, m//2+1):
                b = m-a
                d = gcd(a,b)
                val = proper_biclique(a//d,b//d)**d*4**r-maximum_order(lcm(a,b),r)
                expected.append(('cross', (a,b,r), val))
        got = sorted(map(canonical, entry['rows']))
        check(got == sorted(expected), f'Incomplete or incorrect certificate at {n}')
        count += len(got)
        ordered = sorted(expected, key=lambda x:x[2])
        if n <= 6:
            check(ordered[0][2] == {4:80,5:198,6:570}[n], f'Small bound {n}')
        else:
            a = max(i for i in range(1,n//2+1) if gcd(i,n-i)==1)
            b = n-a
            target = proper_biclique(a,b)-a*b
            check(ordered[0] == ('cross',(a,b,0),target), f'Wrong minimum {n}')
            check(ordered[1][2] > target+a*b, f'Stability gap {n}')
    return count


def integer_orbit(p: list[int], s: list[int], tau: list[int]) -> int:
    n = len(tau)
    initial = sum(c << (2*i) for i,c in enumerate(tau))
    seen = bytearray(1 << (2*n))
    seen[initial] = 1
    queue = array('I', [initial])
    offset = 0
    while offset < len(queue):
        state = queue[offset]; offset += 1
        for transformation in (p,s):
            target = 0
            for i,j in enumerate(transformation):
                target |= ((state >> (2*j)) & 3) << (2*i)
            if not seen[target]:
                seen[target] = 1; queue.append(target)
    return len(queue)


def main() -> None:
    count = check_finite()
    bfs = json.loads((ROOT/'data/bfs_witnesses.json').read_text())
    records = []
    for entry in bfs:
        if entry['n'] > 8:
            continue
        value = integer_orbit(entry['p'],entry['s'],entry['tau'])
        check(value == entry['reverse_states'], f'Integer BFS {entry["n"]}')
        records.append(dict(n=entry['n'], reverse_states=value))
    check(328*3**13 < 9*4**13, 'Threshold-26 arithmetic')
    check(2*5**10 > 17*4**10, 'Cycle exclusion arithmetic')
    result = dict(status='PASS', structural_entries_recomputed=count,
                  finite_n=[4,25], independent_integer_bfs=records,
                  no_import_from_producer=True)
    (ROOT/'data/independent_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
