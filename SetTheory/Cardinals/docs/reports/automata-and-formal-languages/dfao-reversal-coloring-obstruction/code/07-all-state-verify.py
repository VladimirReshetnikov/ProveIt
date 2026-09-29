#!/usr/bin/env python3
"""Exact certificate producer and regression tests for four-output reversal.

Python 3.10+, standard library only. Run from any working directory.
The finite certificate is part of the proof for 4 <= n <= 25.
BFS, inventory and recurrence tests are additional finite checks, not
substitutes for the mathematical infinite-tail argument.
"""
from __future__ import annotations

import csv
import json
from collections import deque
from functools import lru_cache
from itertools import product
from math import gcd, lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def split(n: int) -> tuple[int, int]:
    if n < 7:
        raise ValueError('The split formula in this function requires n >= 7.')
    h = n // 2
    if n % 2:
        return h, h + 1
    delta = 1 if h % 2 == 0 else 2
    return h - delta, h + delta


def biclique(a: int, b: int) -> int:
    if min(a, b) < 1:
        raise ValueError('Biclique sides must be positive.')
    return 6 * 2**(a+b) + 4 * (3**a + 3**b) - 12 * (2**a + 2**b) + 12


def defect(n: int) -> int:
    if n in (4, 5, 6):
        return {4: 80, 5: 198, 6: 570}[n]
    a, b = split(n)
    return biclique(a, b) - a*b


@lru_cache(None)
def permutation_orders(n: int, minimum: int = 1) -> tuple[int, ...]:
    """Orders of permutations on n points, via nondecreasing partitions."""
    if n == 0:
        return (1,)
    return tuple(sorted({lcm(i, o)
                         for i in range(minimum, n+1)
                         for o in permutation_orders(n-i, i)}))


@lru_cache(None)
def residual_order(r: int, t: int) -> int:
    return max(lcm(t, o) for o in permutation_orders(r))


def candidates(n: int) -> list[dict]:
    """Every structural bound in equations (finite collection)."""
    rows = [dict(kind='permutations', parameters=[], deficit=3*4**(n-1)),
            dict(kind='singulars', parameters=[], deficit=9*4**(n-2)-1)]
    for m in range(2, n+1):
        for d in range(1, m):
            if m % d == 0:
                length, r = m // d, n-m
                count = (3**length + (-1)**length*3)**d * 4**r
                rows.append(dict(kind='same', parameters=[m, d, r],
                                 deficit=count-residual_order(r, m)))
    for a in range(1, n):
        for b in range(a, n-a+1):
            d, r = gcd(a, b), n-a-b
            count = biclique(a//d, b//d)**d * 4**r
            rows.append(dict(kind='cross', parameters=[a, b, r],
                             deficit=count-residual_order(r, lcm(a, b))))
    return rows


def witness(n: int) -> tuple[list[int], list[int], tuple[int, ...]]:
    if n == 4:
        return [1, 2, 3, 0], [0, 0, 3, 2], (0, 1, 2, 3)
    if n == 5:
        return [1, 0, 3, 4, 2], [2, 1, 2, 3, 0], (0, 1, 2, 3, 3)
    if n == 6:
        return [1, 2, 3, 4, 5, 0], [0, 3, 0, 4, 5, 1], (0, 0, 1, 1, 2, 3)
    a, b = split(n)
    p = list(range(1, a)) + [0] + list(range(a+1, n)) + [a]
    s = list(range(n))
    s[0], s[-1] = a, 0
    if a % 2:
        s[1], s[2] = 2, 1
    tau = (0,)*(a-1) + (1,) + (2,)*(b-1) + (3,)
    return p, s, tau


def orbit(p: list[int], s: list[int], tau: tuple[int, ...]) -> set[tuple[int, ...]]:
    found = {tau}
    queue = deque([tau])
    while queue:
        c = queue.popleft()
        for f in (p, s):
            v = tuple(c[i] for i in f)
            if v not in found:
                found.add(v)
                queue.append(v)
    return found


def accessible(p: list[int], s: list[int]) -> bool:
    found, todo = {0}, [0]
    for q in todo:
        for f in (p, s):
            if f[q] not in found:
                found.add(f[q]); todo.append(f[q])
    return len(found) == len(p)


def minimal(p: list[int], s: list[int], tau: tuple[int, ...]) -> bool:
    classes = list(tau)
    while True:
        signatures = [(classes[q], classes[p[q]], classes[s[q]]) for q in range(len(p))]
        coding = {sig: i for i, sig in enumerate(sorted(set(signatures)))}
        newer = [coding[sig] for sig in signatures]
        if len(set(newer)) == len(set(classes)):
            return len(set(newer)) == len(p)
        classes = newer


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n+1) if n % d == 0]


def mobius(n: int) -> int:
    sign, d = 1, 2
    while d*d <= n:
        if n % d == 0:
            n //= d; sign = -sign
            if n % d == 0:
                return 0
            while n % d == 0:
                n //= d
        d += 1
    return -sign if n > 1 else sign


def primitive(q: int, n: int) -> int:
    return sum(mobius(n//d) * q**d for d in divisors(n))


def inventory(a: int, b: int) -> list[dict]:
    rows = []
    for u in divisors(a):
        for v in divisors(b):
            if u == v == 1:
                count = 12
            elif u == 1:
                count = 4*primitive(3, v)
            elif v == 1:
                count = 4*primitive(3, u)
            else:
                count = 6*primitive(2, u)*primitive(2, v)
            generic = sum(mobius(u//d)*mobius(v//e)*biclique(d, e)
                          for d in divisors(u) for e in divisors(v))
            require(count == generic, f'Primitive formula mismatch at {(u,v)}')
            require(count % (u*v) == 0, 'Nonintegral orbit count')
            missing_orbits = count//(u*v) - int((u, v) == (a, b))
            rows.append(dict(left_period=u, right_period=v, length=u*v,
                             proper_colorings=count, missing_orbits=missing_orbits))
    require(sum(row['proper_colorings'] for row in rows) == biclique(a, b), 'Inventory sum')
    require(sum(row['length']*row['missing_orbits'] for row in rows) == biclique(a, b)-a*b,
            'Missing inventory sum')
    return rows


def poly_multiply(a: list[int], b: list[int]) -> list[int]:
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return c


def main() -> None:
    DATA.mkdir(exist_ok=True)
    certificates, summaries = [], []
    for n in range(4, 26):
        rows = candidates(n)
        ordered = sorted(rows, key=lambda row: row['deficit'])
        best = ordered[0]
        require(best['deficit'] == defect(n), f'Bad minimum at n={n}')
        require(ordered[1]['deficit'] > best['deficit'], f'Nonunique minimum at {n}')
        if n >= 7:
            a, b = split(n)
            require(best['kind'] == 'cross' and best['parameters'] == [a, b, 0], 'Bad minimizer')
            require(ordered[1]['deficit'] - defect(n) > a*b, 'Stability gap too small')
        certificates.append(dict(n=n, rows=rows))
        summaries.append(dict(n=n, candidates=len(rows), minimum=best['deficit'],
                              kind=best['kind'], parameters=str(best['parameters']),
                              second=ordered[1]['deficit'], gap=ordered[1]['deficit']-best['deficit'],
                              maximum=4**n-best['deficit']))
    (DATA/'finite_certificate.json').write_text(json.dumps(certificates, indent=2)+'\n')
    with (DATA/'finite_summary.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(summaries[0]))
        writer.writeheader(); writer.writerows(summaries)

    bfs = []
    for n in range(4, 10):
        p, s, tau = witness(n)
        reached = orbit(p, s, tau)
        require(len(reached) == 4**n-defect(n), f'Wrong witness orbit at n={n}')
        require(accessible(p, s) and minimal(p, s, tau), f'Bad original automaton at n={n}')
        record = dict(n=n, p=p, s=s, tau=tau, reverse_states=len(reached),
                      accessible=True, minimal=True)
        if 7 <= n <= 8:
            a, b = split(n)
            proper = {c for c in product(range(4), repeat=n) if set(c[:a]).isdisjoint(c[a:])}
            require(len(proper) == biclique(a, b), 'Proper count')
            require(len(proper & reached) == a*b, 'Proper reachable orbit')
            require(len(reached | proper) == 4**n, 'Improper saturation')
            missing = proper-reached
            actual = {}
            while missing:
                c = next(iter(missing)); cycle = set(); v = c
                while v not in cycle:
                    cycle.add(v); v = tuple(v[i] for i in p)
                require(cycle <= missing, 'Missing set not invariant')
                missing.difference_update(cycle)
                actual[len(cycle)] = actual.get(len(cycle), 0) + 1
            expected = {r['length']:r['missing_orbits'] for r in inventory(a, b)
                        if r['missing_orbits']}
            require(actual == expected, f'Orbit inventory at n={n}')
            record['missing_orbit_inventory'] = actual
        bfs.append(record)
    (DATA/'bfs_witnesses.json').write_text(json.dumps(bfs, indent=2)+'\n')

    inventories = {str(n): inventory(*split(n)) for n in range(7, 101)}
    (DATA/'orbit_inventories.json').write_text(json.dumps(inventories, indent=2)+'\n')

    # Q(z)=(1-2z)(1-9z^4)(1-4z^4)(1-z)^2(1-z^4).
    q = [1]
    for factor in ([1,-2], [1,0,0,0,-9], [1,0,0,0,-4], [1,-2,1], [1,0,0,0,-1]):
        q = poly_multiply(q, factor)
    for n in range(22, 501):
        require(sum(q[j]*defect(n-j) for j in range(16)) == 0, f'Recurrence at {n}')
    numerator = [sum(q[j]*defect(7+i-j) for j in range(i+1)) for i in range(15)]
    (DATA/'recurrence.json').write_text(json.dumps(dict(denominator_ascending=q,
        tail_start=7, numerator_ascending=numerator,
        initial_deficits=[defect(n) for n in range(7,22)]), indent=2)+'\n')
    require(328*3**13 < 9*4**13, 'Tail target constant')
    require(2*5**10 > 17*4**10, 'Cycle exclusion constant')
    result = dict(status='PASS', finite_n=[4,25], finite_rows=sum(s['candidates'] for s in summaries),
                  finite_instances=len(summaries), bfs_n=[4,9], exact_inventory_bfs_n=[7,8],
                  algebraic_inventory_n=[7,100], recurrence_n=[22,500],
                  proof_tail='Analytic argument in article; no extrapolation from tests.')
    (DATA/'verification_summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
