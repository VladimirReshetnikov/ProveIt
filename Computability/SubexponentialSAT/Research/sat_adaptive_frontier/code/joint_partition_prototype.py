#!/usr/bin/env python3
"""Finite exact prototype for joint partition selection and cached block sums.

This is a correctness prototype, not a subexponential SAT solver. The final
triangle is summed literally; the fast matrix backend of the theorem is
not implemented. Tests compare against a separately evaluated full sum.
Only Python's standard library is used.
"""
from fractions import Fraction
from itertools import combinations, product
from math import prod
from pathlib import Path
from random import Random
import json


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def add(x, y):
    return ((x[0] + y[0]) % 64, (x[1] + y[1]) % 64)


def mul(x, y):
    return ((x[0] * y[0]) % 64, (x[0] * y[1] + x[1] * y[0]) % 64)


def equipartitions(r):
    """Yield every unlabelled equal three-block partition exactly once."""
    require(r % 3 == 0, 'three equal blocks required')
    k = r // 3
    vertices = set(range(r))
    for aa in combinations(range(r), k):
        if 0 not in aa:
            continue
        remaining = sorted(vertices - set(aa))
        for bb in combinations(remaining, k):
            cc = tuple(sorted(set(remaining) - set(bb)))
            if bb < cc:
                yield (aa, bb, cc)


def joint_score(blocks, sizes):
    """Return 2^(5 W), exactly as a rational number; no logarithms."""
    sets = [set(b) for b in blocks]
    incident = [prod(n for (u, v), n in sizes.items() if u in b or v in b)
                for b in sets]
    cross = [prod(sizes[u, v] * sizes[v, u] for u in sets[a] for v in sets[b])
             for a, b in combinations(range(3), 2)]
    triangle = Fraction(prod(cross) ** 5, min(cross) ** 3)
    return max([Fraction(n ** 5) for n in incident] + [triangle])


def select_partition(r, sizes):
    return min(equipartitions(r), key=lambda p: joint_score(p, sizes))


def literal_contraction(r, sizes, factors):
    edges = sorted(sizes)
    total = (0, 0)
    for values in product(*(range(sizes[e]) for e in edges)):
        assignment = dict(zip(edges, values))
        term = (1, 0)
        for v in range(r):
            axes, table = factors[v]
            term = mul(term, table[tuple(assignment[e] for e in axes)])
        total = add(total, term)
    return total


def cached_contraction(r, sizes, factors):
    blocks = select_partition(r, sizes)
    caches = {}
    calls = [0] * r
    for v in range(r):
        axes, original = factors[v]
        cache = {}
        for values in product(*(range(sizes[e]) for e in axes)):
            cache[values] = original[values]
            calls[v] += 1
        caches[v] = (axes, cache)
    block_tables = []
    construction_visits = []
    for block in blocks:
        bb = set(block)
        boundary = sorted(e for e in sizes if (e[0] in bb) != (e[1] in bb))
        internal = sorted(e for e in sizes if e[0] in bb and e[1] in bb)
        table = {}
        visits = 0
        for bv in product(*(range(sizes[e]) for e in boundary)):
            assignment = dict(zip(boundary, bv))
            total = (0, 0)
            for iv in product(*(range(sizes[e]) for e in internal)):
                assignment.update(zip(internal, iv))
                term = (1, 0)
                for v in block:
                    axes, cache = caches[v]
                    term = mul(term, cache[tuple(assignment[e] for e in axes)])
                total = add(total, term)
                visits += 1
            table[bv] = total
        block_tables.append((boundary, table))
        construction_visits.append(visits)
        require(visits == prod(sizes[e] for e in boundary + internal),
                'block construction was not fully counted')
    crossing = sorted(set(e for axes, _ in block_tables for e in axes))
    total = (0, 0)
    for values in product(*(range(sizes[e]) for e in crossing)):
        assignment = dict(zip(crossing, values))
        term = (1, 0)
        for axes, table in block_tables:
            term = mul(term, table[tuple(assignment[e] for e in axes)])
        total = add(total, term)
    return total, calls, construction_visits, blocks


def main():
    rng = Random(461922)
    checked = 0
    group_calls = 0
    build_visits = 0
    partition_counts = {}
    for r in (6, 9):
        ps = list(equipartitions(r))
        partition_counts[r] = len(ps)
        require(len(ps) == {6: 15, 9: 280}[r], 'partition count')
        edges = [(a, b) for a in range(r) for b in range(r) if a != b]
        for _ in range(12):
            active = set(rng.sample(edges, 7))
            sizes = {e: 2 if e in active else 1 for e in edges}
            factors = {}
            for v in range(r):
                axes = sorted(e for e in edges if v in e)
                table = {vals: (rng.randrange(64), rng.randrange(64))
                         for vals in product(*(range(sizes[e]) for e in axes))}
                factors[v] = (axes, table)
            got, calls, visits, chosen = cached_contraction(r, sizes, factors)
            require(got == literal_contraction(r, sizes, factors), 'finite sum differs')
            require(joint_score(chosen, sizes) == min(joint_score(p, sizes) for p in ps),
                    'partition is not an exact minimizer')
            for v in range(r):
                require(calls[v] == prod(sizes[e] for e in factors[v][0]),
                        'group oracle calls not fully counted')
            group_calls += sum(calls)
            build_visits += sum(visits)
            checked += 1
    result = {'status': 'PASS', 'exact_finite_contractions': checked,
              'unlabelled_partition_counts': partition_counts,
              'group_oracle_calls_checked': group_calls,
              'block_construction_visits_checked': build_visits,
              'ring': '(Z/64Z)[V]/(V^2)',
              'limitation': 'Final triangle uses literal summation; fast-matrix runtime is not benchmarked.'}
    target = Path(__file__).resolve().parents[1] / 'results' / 'joint_prototype_checks.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
