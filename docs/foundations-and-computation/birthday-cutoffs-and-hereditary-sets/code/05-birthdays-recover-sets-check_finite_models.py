#!/usr/bin/env python3
"""Finite consistency checks for Birthdays Recover Sets.

These tests check finite analogues, not the transfinite reconstruction theorem.
Python 3.10+, standard library only. Run from any directory.
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import json

Sign = tuple[int, ...]

def cmp_sign(a: Sign, b: Sign) -> int:
    for k in range(max(len(a), len(b))):
        av = a[k] if k < len(a) else 0
        bv = b[k] if k < len(b) else 0
        if av != bv:
            return 1 if av > bv else -1
    return 0

def check_prefix(max_length: int = 7) -> dict[str, int]:
    signs = [tuple(t) for n in range(max_length + 1)
             for t in product((-1, 1), repeat=n)]
    # The witness quantifier needs only strings of birthday <= birthday(y).
    # Sorting turns strict betweenness into an interval of this finite list.
    from functools import cmp_to_key
    signs.sort(key=cmp_to_key(cmp_sign))
    count = 0
    for i, y in enumerate(signs):
        for j, x in enumerate(signs):
            lo, hi = sorted((i, j))
            older_between = any(len(z) <= len(y) for z in signs[lo+1:hi])
            formula = len(y) <= len(x) and not older_between
            actual = x[:len(y)] == y
            assert formula == actual, (y, x)
            count += 1
    # Removing the birthday inequality breaks the criterion at y=1, x=0.
    y, x = (1,), ()
    assert not any(cmp_sign(x, z) < 0 and cmp_sign(z, y) < 0
                   and len(z) <= len(y) for z in signs)
    assert x[:len(y)] != y
    return {'strings': len(signs), 'ordered_pairs': count,
            'maximum_birthday': max_length}

def decode(graph: tuple[frozenset[int], ...]) -> tuple[frozenset, ...]:
    values: list[frozenset] = []
    for i, children in enumerate(graph):
        assert all(j < i for j in children)
        values.append(frozenset(values[j] for j in children))
    return tuple(values)

def bisimulation(g: tuple[frozenset[int], ...],
                 h: tuple[frozenset[int], ...]) -> set[tuple[int,int]]:
    rel = {(i,j) for i in range(len(g)) for j in range(len(h))}
    while True:
        keep = {(i,j) for i,j in rel
                if all(any((a,b) in rel for b in h[j]) for a in g[i])
                and all(any((a,b) in rel for a in g[i]) for b in h[j])}
        if keep == rel:
            return rel
        rel = keep

def all_dags(n: int):
    pairs = [(i,j) for j in range(n) for i in range(j)]
    for mask in range(1 << len(pairs)):
        children: list[set[int]] = [set() for _ in range(n)]
        for k,(i,j) in enumerate(pairs):
            if mask & (1 << k):
                children[j].add(i)
        yield tuple(frozenset(ch) for ch in children)

def check_graphs(n: int = 4) -> dict[str,int]:
    graphs = list(all_dags(n))
    comparisons = 0
    node_pairs = 0
    for g in graphs:
        gv = decode(g)
        for h in graphs:
            hv = decode(h)
            rel = bisimulation(g,h)
            for i in range(n):
                for j in range(n):
                    assert ((i,j) in rel) == (gv[i] == hv[j])
                    encoded_member = any((i,k) in rel for k in h[j])
                    assert encoded_member == (gv[i] in hv[j])
                    node_pairs += 1
            comparisons += 1
    # Padding in the matrix code is false; edges point child -> parent.
    code_count = 0
    for g in graphs:
        code = [False] * (n * (n+1))
        for j,children in enumerate(g):
            for i in children:
                code[n*j+i] = True
        recovered = tuple(frozenset(i for i in range(n) if code[n*j+i])
                          for j in range(n))
        assert recovered == g
        code_count += 1
    return {'acyclic_graphs': len(graphs), 'graph_pairs': comparisons,
            'root_pair_checks_each_for_equality_and_membership': node_pairs,
            'matrix_roundtrips': code_count}

def check_rows() -> dict[str,int]:
    tests = 0
    for width in range(1,8):
        for height in range(1,8):
            indexes = [width*j+i for j in range(height) for i in range(width)]
            assert len(indexes) == len(set(indexes))
            assert all(0 <= p < width*(height+1) for p in indexes)
            tests += 1
    # All finite row lists are complete exactly when no new row is witnessed.
    detector_tests = 0
    for width in range(1,5):
        universe = list(product((False,True), repeat=width))
        for missing in universe:
            old = [r for r in universe if r != missing]
            detected = [x for x in universe if all(x != row for row in old)]
            assert detected == [missing]
            detector_tests += 1
    return {'packing_rectangles': tests, 'row_detector_tests': detector_tests}

def main() -> None:
    out = {'status': 'all finite checks passed; not a transfinite proof',
           'prefix': check_prefix(), 'graphs': check_graphs(), 'rows': check_rows()}
    path = Path(__file__).resolve().parents[1] / 'data' / 'finite_checks.json'
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out, indent=2))

if __name__ == '__main__':
    main()
