#!/usr/bin/env python3
"""Independent finite checks and cross-checks for ordinal_maps.py.

These checks test finite instances and implementation agreement; they do not
constitute a formal proof of any transfinite assertion.
"""
from __future__ import annotations
import csv
import json
import platform
import random
from itertools import combinations
from pathlib import Path
from time import perf_counter

from ordinal_maps import (
    ZERO, ONE, OMEGA, Ordinal, Poset, omega_power, natural_sum,
    order_map_type, order_map_type_direct, order_map_height,
    grid_powerset_type, grid_powerset_height, examples,
)

ROOT = Path(__file__).resolve().parents[1]


def natural_posets(n: int):
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        rows = [0] * n
        for k, (i, j) in enumerate(pairs):
            if mask & (1 << k):
                rows[i] |= 1 << j
        if all(not (rows[i] & (1 << j)) or not (rows[j] & ~rows[i])
               for i in range(n) for j in range(n)):
            yield Poset(n, tuple(rows))


def finite_rank_check(p: Poset, colours: int) -> int:
    values = sorted(p.maps(colours), key=lambda v: (sum(v), v))
    ranks: dict[tuple[int, ...], int] = {}
    # This uses all predecessors, independently of the rank formula.
    for v in values:
        rank = max((r+1 for u, r in ranks.items()
                    if all(a <= b for a, b in zip(u, v))), default=0)
        assert rank == sum(v), (p, colours, v, rank)
        ranks[v] = rank
    height = max((r+1 for r in ranks.values()), default=0)
    assert order_map_height(p.n, Ordinal.finite(colours)) == Ordinal.finite(height)
    return len(values)


def downset_check(p: Poset, length: int) -> tuple[int, int]:
    n = p.n
    vertices = [(x, i) for x in range(length) for i in range(n)]
    principal = []
    for y, j in vertices:
        mask = 0
        for k, (x, i) in enumerate(vertices):
            if x <= y and (i == j or p.successors[i] & (1 << j)):
                mask |= 1 << k
        principal.append(mask)
    closures: set[int] = set()
    for subset in range(1 << len(vertices)):
        closure = 0
        for k, down in enumerate(principal):
            if subset & (1 << k):
                closure |= down
        closures.add(closure)
    encoded = {}
    for closure in closures:
        v = tuple(sum(bool(closure & (1 << k)) for k, (_, i) in enumerate(vertices)
                      if i == j) for j in range(n))
        encoded[closure] = v
    assert len(set(encoded.values())) == len(closures)
    assert set(encoded.values()) == set(p.dual().maps(length + 1))
    for a, x in encoded.items():
        for b, y in encoded.items():
            assert (a & ~b == 0) == all(i <= j for i, j in zip(x, y))
    expected = Ordinal.finite(len(closures))
    assert grid_powerset_type(p, Ordinal.finite(length)) == expected
    return 1 << len(vertices), len(closures)


def arithmetic_tests() -> int:
    pool = [ZERO, ONE, Ordinal.finite(2), Ordinal.finite(3), OMEGA,
            OMEGA.ordinary_sum(ONE), OMEGA.natural_times(2),
            omega_power(Ordinal.finite(2)), omega_power(OMEGA),
            omega_power(OMEGA.ordinary_sum(ONE))]
    rng = random.Random(20260919)
    checked = 0
    for _ in range(400):
        a, b, c = [rng.choice(pool) for _ in range(3)]
        assert a.natural_sum(b) == b.natural_sum(a)
        assert a.natural_sum(b).natural_sum(c) == a.natural_sum(b.natural_sum(c))
        assert a.natural_product(b) == b.natural_product(a)
        assert a.natural_product(b).natural_product(c) == a.natural_product(b.natural_product(c))
        assert a.natural_product(b.natural_sum(c)) == a.natural_product(b).natural_sum(a.natural_product(c))
        assert a.ordinary_sum(b).ordinary_sum(c) == a.ordinary_sum(b.ordinary_sum(c))
        assert Ordinal.from_json(a.to_json()) == a
        if a < b:
            assert a.natural_sum(c) < b.natural_sum(c)
        checked += 1
    assert ONE.ordinary_sum(OMEGA) == OMEGA
    assert OMEGA.ordinary_sum(ONE) != OMEGA
    assert OMEGA.ordinary_sum(ONE).natural_times(2) == OMEGA.natural_times(2).ordinary_sum(Ordinal.finite(2))
    assert order_map_height(3, OMEGA.natural_times(2)) == OMEGA.natural_times(4)
    assert order_map_height(3, OMEGA.ordinary_sum(ONE)) == OMEGA.natural_times(3).ordinary_sum(ONE)
    # Validate failures for malformed input.
    for bad in [-1, {'cnf': [[0, 0]]}, {'cnf': [[0, 1], [1, 1]]}]:
        try:
            Ordinal.from_json(bad)
        except (ValueError, TypeError):
            pass
        else:
            raise AssertionError('Malformed ordinal was accepted.')
    try:
        Poset.from_edges(2, [(0, 1), (1, 0)])
    except ValueError:
        pass
    else:
        raise AssertionError('Cyclic relation was accepted.')
    return checked


def main() -> None:
    start = perf_counter()
    out = ROOT / 'data'
    out.mkdir(exist_ok=True)
    summary = {
        'date': '2026-09-19', 'python_version': platform.python_version(),
        'scope': 'Naturally labelled posets with at most five vertices; not isomorphism classes.',
        'posets_by_size': {}, 'finite_map_cases': 0, 'finite_map_rank_checks': 0,
        'symbolic_direct_dp_cases': 0, 'finite_hoare_cases': 0,
        'finite_subsets_enumerated': 0, 'finite_downset_classes': 0,
        'arithmetic_random_triples': arithmetic_tests(),
        'failed_assertions': 0,
        'caveat': 'Finite checks and implementation agreement do not prove transfinite theorems.'
    }
    rows = []
    symbolic = [OMEGA, OMEGA.ordinary_sum(ONE), OMEGA.natural_times(2),
                omega_power(Ordinal.finite(2)).ordinary_sum(OMEGA).ordinary_sum(ONE),
                omega_power(OMEGA.ordinary_sum(ONE)).ordinary_sum(omega_power(OMEGA)).ordinary_sum(ONE)]
    for n in range(6):
        posets = list(natural_posets(n))
        summary['posets_by_size'][str(n)] = len(posets)
        for index, p in enumerate(posets):
            for colours in range(5):
                count = finite_rank_check(p, colours)
                beta = Ordinal.finite(colours)
                assert order_map_type(p, beta) == Ordinal.finite(count)
                assert order_map_type_direct(p, beta) == Ordinal.finite(count)
                summary['finite_map_cases'] += 1
                summary['finite_map_rank_checks'] += count
                rows.append([n, index, colours, count, str(order_map_height(n, beta))])
            for beta in symbolic:
                assert order_map_type(p, beta) == order_map_type_direct(p, beta)
                summary['symbolic_direct_dp_cases'] += 1
            if n <= 4:
                for length in range(3):
                    subsets, classes = downset_check(p, length)
                    summary['finite_hoare_cases'] += 1
                    summary['finite_subsets_enumerated'] += subsets
                    summary['finite_downset_classes'] += classes
    assert list(summary['posets_by_size'].values()) == [1, 1, 2, 7, 40, 357]
    example_data = examples()
    assert example_data['fork']['finite_order_map_counts_1_to_5'] == example_data['dual_fork']['finite_order_map_counts_1_to_5']
    assert example_data['fork']['powerset_maximal_order_type'] != example_data['dual_fork']['powerset_maximal_order_type']
    summary['elapsed_seconds'] = round(perf_counter() - start, 3)
    (out / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    (out / 'examples.json').write_text(json.dumps(example_data, indent=2) + '\n')
    with (out / 'finite_checks.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['vertices', 'natural_poset_index', 'codomain_size', 'isotone_maps', 'height'])
        writer.writerows(rows)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Verification requires assertions; do not use python -O.')
    main()
