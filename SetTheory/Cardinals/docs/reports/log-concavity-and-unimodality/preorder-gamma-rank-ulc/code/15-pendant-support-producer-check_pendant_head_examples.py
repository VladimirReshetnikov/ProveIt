#!/usr/bin/env python3
"""Exact physical-support and negative-root checks for the explicit HPP subclass."""
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random


def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def divrem(a, b):
    a = list(map(Fraction, a))
    b = trim(list(map(Fraction, b)))
    q = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    while a != [0] and len(a) >= len(b):
        k = len(a) - len(b)
        t = a[-1] / b[-1]
        q[k] = t
        for j in range(len(b)):
            a[j+k] -= t*b[j]
        trim(a)
    return trim(q), trim(a)


def derivative(p):
    return trim([i*p[i] for i in range(1, len(p))] or [0])


def negative_real_root_check(p):
    p = trim(list(map(Fraction, p)))
    if len(p) == 1:
        return 0
    a, b = p, derivative(p)
    while b != [0]:
        a, b = b, divrem(a, b)[1]
    squarefree = divrem(p, a)[0]
    sequence = [squarefree, derivative(squarefree)]
    while sequence[-1] != [0]:
        r = divrem(sequence[-2], sequence[-1])[1]
        if r == [0]:
            break
        sequence.append([-x for x in r])
    def variations(signs):
        signs = [s for s in signs if s]
        return sum(a != b for a, b in zip(signs, signs[1:]))
    def sign(x):
        return (x > 0) - (x < 0)
    minus_infinity = [sign(q[-1]) * (-1 if (len(q)-1) % 2 else 1)
                      for q in sequence]
    at_zero = [sign(q[0]) for q in sequence]
    count = variations(minus_infinity) - variations(at_zero)
    assert count == len(squarefree)-1, (p, count, squarefree)
    return count


def support_coefficients(n, arcs, u, v):
    # Build actual physical matchings, deduplicating ordered supports after
    # every step. An edge can be added exactly when its physical ends are free.
    supports = {(0, 0)}
    for i, j in sorted(set(arcs)):
        for s, t in list(supports):
            if not ((s | t) & ((1 << i) | (1 << j))):
                supports.add((s | (1 << i), t | (1 << j)))
    coefficients = [0] * (n//2 + 1)
    for s, t in supports:
        weight = 1
        for i in range(n):
            if s & (1 << i):
                weight *= u[i]
            if t & (1 << i):
                weight *= v[i]
        coefficients[s.bit_count()] += weight
    return trim(coefficients)


def main():
    rng = random.Random(235010032026)
    count = 0
    zero_faces = 0
    overlap_counts = [0, 0, 0]
    max_degree = 0
    for overlap in range(3):
        P = {0, 1}
        Q = [{2,3,4}, {1,2,3}, {0,1,2}][overlap]
        for trial in range(160):
            n = 8 + trial % 3
            arcs = []
            for i in range(n):
                choices = [set()] + [{q} for q in sorted(Q) if q != i]
                if i not in Q:
                    choices.append(Q)
                for j in rng.choice(choices):
                    arcs.append((i, j))
            for j in range(n):
                if j in Q:
                    continue
                choices = [-1] + [i for i in sorted(P) if i != j]
                i = rng.choice(choices)
                if i >= 0:
                    arcs.append((i, j))
            u = [rng.randrange(6) for _ in range(n)]
            v = [rng.randrange(6) for _ in range(n)]
            g = support_coefficients(n, arcs, u, v)
            negative_real_root_check(g)
            d = len(g)-1
            for k in range(1, d):
                assert k*(d-k)*g[k]**2 >= (k+1)*(d-k+1)*g[k-1]*g[k+1]
            count += 1
            overlap_counts[overlap] += 1
            max_degree = max(max_degree, d)
            zero_faces += int(0 in u+v)
    # A non-bipartite physical example with overlapping role cover.
    n = 9
    P, Q = [0,1], [1,2,3]
    arcs = [(0,q) for q in Q] + [(1,2), (1,0), (0,7), (1,8)]
    arcs += [(i,q) for i in [4,5,6] for q in Q]
    g = support_coefficients(n, arcs, [1]*n, [1]*n)
    negative_real_root_check(g)
    result = {
        "result": "all examples have only negative real roots by exact rational Sturm counts",
        "random_cases": count,
        "by_role_cover_overlap": overlap_counts,
        "zero_activity_cases": zero_faces,
        "maximum_surviving_degree": max_degree,
        "seed": 235010032026,
        "nonbipartite_example": {
            "vertices": list(range(n)), "tail_cover": P, "head_cover": Q,
            "arcs": sorted(set(arcs)), "activities": "all one",
            "support_polynomial_coefficients": g,
            "physical_triangle": [0,1,2]
        },
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    }
    Path(__file__).with_name("pendant_verification.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
