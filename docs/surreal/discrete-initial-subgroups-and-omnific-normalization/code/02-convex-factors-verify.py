#!/usr/bin/env python3
"""Exact finite regression checks for Convex Factors and Profinite Obstructions.

These checks do not prove the transfinite or model-theoretic theorems.
Python 3.10+; standard library only. Run from any directory.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations, product
import json
from math import factorial
from pathlib import Path

Sign = tuple[int, ...]

def compare(x: Sign, y: Sign) -> int:
    for k in range(max(len(x), len(y))):
        a = x[k] if k < len(x) else 0
        b = y[k] if k < len(y) else 0
        if a != b:
            return (a > b) - (a < b)
    return 0

def prefix(x: Sign, y: Sign) -> bool:
    return len(x) < len(y) and y[:len(x)] == x

def meet(x: Sign, y: Sign) -> Sign:
    k = 0
    while k < min(len(x), len(y)) and x[k] == y[k]:
        k += 1
    return x[:k]

def tree(depth: int) -> list[Sign]:
    return sorted([s for k in range(depth + 1)
                   for s in product((-1, 1), repeat=k)], key=cmp_to_key(compare))

def compress(x: Sign, domain: set[Sign]) -> Sign:
    if x not in domain:
        raise ValueError("Compression is defined here only on its domain")
    return tuple(sign for k, sign in enumerate(x) if x[:k] in domain)

def check_domain(domain: set[Sign], counts: Counter) -> None:
    image = {x: compress(x, domain) for x in domain}
    target = set(image.values())
    assert len(target) == len(domain)
    for x, cx in image.items():
        for k in range(len(cx)):
            assert cx[:k] in target
            counts['initial_image_prefix_checks'] += 1
        for y, cy in image.items():
            assert compare(x, y) == compare(cx, cy)
            assert prefix(x, y) == prefix(cx, cy)
            assert image[meet(x, y)] == meet(cx, cy)
            counts['order_prefix_meet_pair_checks'] += 1
    counts['compression_domains'] += 1

def check_compression(counts: Counter) -> None:
    nodes = tree(5)
    for a in range(len(nodes)):
        for b in range(a + 1, len(nodes) + 1):
            check_domain(set(nodes[a:b]), counts)
            counts['convex_intervals_depth_5'] += 1
    small = tree(2)
    for bits in range(1, 1 << len(small)):
        domain = {x for j, x in enumerate(small) if bits & (1 << j)}
        if all(meet(x, y) in domain for x in domain for y in domain):
            check_domain(domain, counts)
            counts['meet_closed_subsets_depth_2'] += 1
    nodes = tree(4)
    for a in range(len(nodes)):
        for b in range(a + 1, len(nodes) + 1):
            outer = set(nodes[a:b])
            first = {x: compress(x, outer) for x in outer}
            for c in range(a, b):
                for d in range(c + 1, b + 1):
                    inner = set(nodes[c:d])
                    transported = {first[x] for x in inner}
                    for x in inner:
                        assert compress(first[x], transported) == compress(x, inner)
                        counts['coherence_point_checks'] += 1
                    counts['nested_interval_pairs_depth_4'] += 1
    bad = {(-1,), (1,)}
    assert compress((-1,), bad) == compress((1,), bad) == ()
    counts['non_meet_closed_counterexamples'] += 1

def check_factorial_extensions(counts: Counter) -> list[dict]:
    residues = {1: 0}
    for n in range(1, 101):
        residues[n + 1] = residues[n] + factorial(n)
    e = (Fraction(0), Fraction(1))
    x = lambda n: (Fraction(1, factorial(n)),
                   Fraction(residues[n], factorial(n)))
    rows = []
    for n in range(1, 101):
        xn, xn1 = x(n), x(n + 1)
        assert tuple((n + 1) * z for z in xn1) == tuple(xn[j] + e[j] for j in (0, 1))
        assert 0 <= residues[n] < factorial(n)
        if n >= 3:
            assert Fraction(residues[n], factorial(n)) <= Fraction(2, n)
        counts['factorial_transition_checks'] += 1
        for m in range(1, n + 1):
            assert (residues[n] - residues[m]) % factorial(m) == 0
            counts['factorial_compatibility_checks'] += 1
        if n <= 9:
            rows.append({'n': n, 'factorial': factorial(n), 'S_n': residues[n],
                         'x_n': [str(z) for z in xn]})
    # At every finite stage there is an integer retraction compatible with
    # all transitions seen so far. This is not a global splitting.
    for N in range(1, 61):
        b1 = -residues[N]
        b = {n: (b1 + residues[n]) // factorial(n) for n in range(1, N + 1)}
        for n in range(1, N + 1):
            assert b1 + residues[n] == factorial(n) * b[n]
            counts['finite_retraction_divisibility_checks'] += 1
        for n in range(1, N):
            assert (n + 1) * b[n + 1] == b[n] + 1
            counts['finite_retraction_relation_checks'] += 1
    # All tested ordinary profinite parameters really split, including negative ones.
    for alpha in range(-30, 31):
        S = {n: alpha % factorial(n) for n in range(1, 31)}
        b = {n: (S[n] - alpha) // factorial(n) for n in S}
        for n in range(1, 30):
            digit = (S[n + 1] - S[n]) // factorial(n)
            assert 0 <= digit <= n
            assert (n + 1) * b[n + 1] == b[n] + digit
            counts['integer_parameter_splitting_checks'] += 1
    return rows

def check_projections(counts: Counter) -> None:
    exponents = list(range(8))
    vectors = [tuple(Fraction(((k + 3) * (j + 1)) % 7 - 3, j + 1)
                     for j in exponents) for k in range(12)]
    intervals = [set(exponents[a:b]) for a in range(9) for b in range(a, 9)]
    def project(v, I):
        return tuple(v[j] if j in I else Fraction(0) for j in exponents)
    for I, J in product(intervals, repeat=2):
        for v in vectors:
            assert project(project(v, I), J) == project(v, I & J)
            counts['projection_composition_checks'] += 1
    for I in intervals:
        for u, v in combinations(vectors, 2):
            uv = tuple(a + b for a, b in zip(u, v))
            assert project(uv, I) == tuple(a + b for a, b in zip(project(u, I), project(v, I)))
            counts['projection_additivity_checks'] += 1

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional JSON output file')
    args = parser.parse_args()
    counts: Counter = Counter()
    check_compression(counts)
    rows = check_factorial_extensions(counts)
    check_projections(counts)
    result = {'status': 'PASS', 'arithmetic': 'exact integers and fractions',
              'scope': 'finite regression only; no transfinite or Lean certification',
              'counts': dict(sorted(counts.items())), 'factorial_example': rows}
    text = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')

if __name__ == '__main__':
    main()
