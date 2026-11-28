#!/usr/bin/env python3
"""Exact, independent certificate verifier; uses only Python's standard library.

For each block enumerate its group elements (even symmetric blocks are small),
compute its signed/Ramanujan-weighted cycle inventory, divide out the gcd,
then multiply inventories on disjoint blocks.  No LP or stored rows are trusted.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import gcd, factorial, prod
from pathlib import Path
import json
import sys


def partitions(n, lower=1):
    if n == 0:
        yield ()
    for k in range(lower, n+1):
        for tail in partitions(n-k, k):
            yield (k,) + tail


def cycle_type(p):
    seen = [False] * len(p)
    result = []
    for i in range(len(p)):
        if not seen[i]:
            j, k = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                k += 1
            result.append(k)
    return tuple(sorted(result))


def mobius(n):
    r, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            r = -r
            if n % p == 0:
                return 0
        p += 1
    return -r if n > 1 else r


@lru_cache(None)
def ramanujan(d, j):
    return sum(h * mobius(d//h) for h in range(1, d+1)
               if d % h == 0 and j % h == 0)


def multiply(a, b):
    c = Counter()
    for x, vx in a.items():
        for y, vy in b.items():
            c[tuple(sorted(x+y))] += vx*vy
    return {p: v for p, v in c.items() if v}


@lru_cache(None)
def block(spec):
    family, m, *params = spec
    assert isinstance(m, int) and m >= 1
    inventory = Counter()
    if family == 'S':
        (e,) = params
        assert e in (0, 1)
        for p in permutations(range(m)):
            ct = cycle_type(p)
            inventory[ct] += (-1)**(e*(m-len(ct)))
    elif family == 'C':
        (d,) = params
        assert d >= 1 and m % d == 0
        for j in range(m):
            p = tuple((i+j) % m for i in range(m))
            inventory[cycle_type(p)] += ramanujan(d, j)
    elif family == 'D':
        a, b = params
        assert m >= 3 and a in (0, 1) and b in (0, 1) and (a*m) % 2 == 0
        for j in range(m):
            for h in (0, 1):
                p = tuple(((-1)**h*i+j) % m for i in range(m))
                inventory[cycle_type(p)] += (-1)**(a*j+b*h)
    elif family == 'A':
        u, d = params
        assert 2 <= u < m and gcd(u, m) == 1
        powers = [1]
        while (v := powers[-1]*u % m) != 1:
            assert v not in powers
            powers.append(v)
        assert d >= 1 and len(powers) % d == 0
        for j, v in enumerate(powers):
            for a in range(m):
                p = tuple((v*i+a) % m for i in range(m))
                inventory[cycle_type(p)] += ramanujan(d, j)
    else:
        raise ValueError(f'Unknown block: {spec}')
    g = gcd(*inventory.values())
    assert g > 0 and inventory[(1,)*m] > 0
    return {p: v//g for p, v in inventory.items() if v}


def z(p):
    return prod(k**e * factorial(e) for k, e in Counter(p).items())


def verify(filename):
    c = json.loads(filename.read_text())
    n = c['n']
    assert n >= 3
    total = Counter()
    for term in c['terms']:
        w = Fraction(term['weight'])
        assert w > 0
        assert sum(b[1] for b in term['blocks']) == n
        row = {(): 1}
        for spec in term['blocks']:
            row = multiply(row, block(tuple(spec)))
        # Every individual term is orthogonal to trivial and standard.
        assert sum(row.values()) == 0
        assert sum(v*p.count(1) for p, v in row.items()) == 0
        for p, v in row.items():
            total[p] += w*v
    expected = {p: Fraction(1, z(p)) for p in partitions(n)}
    expected[(1,)*n] += Fraction(n-3, 2)
    expected[(1,)*(n-2)+(2,)] -= Fraction(n-1, 2)
    assert set(total) <= set(expected)
    for p, v in expected.items():
        assert total[p] == v, (n, p, total[p], v)
    print(f'S_{n}: {len(expected)} conjugacy classes, {len(c["terms"])} positive rational terms; EXACT IDENTITY VERIFIED')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O so verification assertions are enabled.')
    paths = [Path(x) for x in sys.argv[1:]] or sorted(Path(__file__).parent.glob('cert*.json'))
    assert paths
    for path in paths:
        verify(path)
