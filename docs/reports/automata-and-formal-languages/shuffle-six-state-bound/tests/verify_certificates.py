#!/usr/bin/env python3
"""Independent standard-library certificate checks and small-lattice audit.

The exhaustive six-row coverage check is src/verify.cpp; this program separately
checks every transition and independently enumerates all families for m <= 4.
"""
from __future__ import annotations
import csv
import itertools
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_certificates(path: Path):
    for lineno, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith('#'):
            continue
        values = list(map(int, line.split()))
        m, n, family = values[:3]
        require(2 <= m <= 6 and m <= n <= 20, f'line {lineno}: dimensions')
        require(len(values) == 3 + m + 2*n, f'line {lineno}: record length')
        require(0 <= family < (1 << (1 << m)), f'line {lineno}: family')
        f = values[3:3+m]
        g = values[3+m:3+m+n]
        t = values[3+m+n:]
        yield m, n, family, f, g, t


def is_core(m: int, columns: list[int]) -> bool:
    if len(columns) < m or len(set(columns)) != len(columns):
        return False
    if any(c.bit_count() < 2 for c in columns):
        return False
    if any(a & b == a for a in columns for b in columns if a != b):
        return False
    rows = [{j for j, c in enumerate(columns) if (c >> i) & 1}
            for i in range(m)]
    return (all(len(r) >= 2 for r in rows)
            and all(not rows[i] <= rows[j]
                    for i in range(m) for j in range(m) if i != j))


def canonical(m: int, columns: list[int]) -> int:
    """Direct canonicalization, independent of the C++ implementation."""
    choices = []
    for p in itertools.permutations(range(m)):
        transformed = [sum(1 << p[i] for i in range(m) if (c >> i) & 1)
                       for c in columns]
        degrees = [sum((c >> i) & 1 for c in transformed) for i in range(m)]
        if degrees == sorted(degrees):
            choices.append(sum(1 << c for c in transformed))
    return min(choices)


def main() -> None:
    expected = {(int(r['m']), int(r['family']))
                for r in csv.DictReader((ROOT/'data/cores.csv').open())}
    found = set()
    count = 0
    for m, n, family, f, g, t in read_certificates(ROOT/'certificates/cores.cert'):
        key = (m, family)
        require(key not in found, f'duplicate {key}')
        found.add(key)
        columns = [c for c in range(1 << m) if (family >> c) & 1]
        require(len(columns) == n and is_core(m, columns), f'not a core: {key}')
        require(sorted(f) == list(range(m)), f'not a permutation: {key}')
        require(all(0 <= x < n for x in g), f'column map: {key}')
        require(all(0 < x < (1 << m) for x in t), f'source column: {key}')
        target = {(i, j) for j, c in enumerate(columns)
                  for i in range(m) if (c >> i) & 1}
        source = {(i, j) for j, c in enumerate(t)
                  for i in range(m) if (c >> i) & 1}
        require({i for i, j in source} == set(range(m)), f'source rows: {key}')
        require({j for i, j in source} == set(range(n)), f'source columns: {key}')
        require(len(source) < len(target), f'not smaller: {key}')
        image = {(f[i], j) for i, j in source} | {(i, g[j]) for i, j in source}
        require(image == target, f'wrong image: {key}')
        count += 1
    require(found == expected, 'certificate keys disagree with manifest')
    print(f'Independent Python transition checks: {count} PASS')
    print('Core conditions, support, cardinalities, permutations, manifest: PASS')
    for m in range(2, 5):
        representatives = set()
        # Deliberately enumerate every family, not the antichain recursion.
        for family in range(1 << (1 << m)):
            columns = [c for c in range(1 << m) if (family >> c) & 1]
            if is_core(m, columns):
                representatives.add(canonical(m, columns))
        require(representatives == {f for r, f in found if r == m},
                f'independent complete enumeration failed at m={m}')
        print(f'Independent all-family enumeration m={m}: '
              f'{len(representatives)} core orbits, PASS')
    print('OVERALL: PASS')


if __name__ == '__main__':
    main()
