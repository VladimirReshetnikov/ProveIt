#!/usr/bin/env python3
"""Exact diagnostic checks for the shared-anchor candidate theorems.

All computations use integer arithmetic modulo explicitly checked primes.
The all-parameter assertions are proved in sections/interpolation.tex.
Run from any directory; a JSON certificate is written beside this script.
"""
from itertools import combinations, combinations_with_replacement, product, permutations
from pathlib import Path
from math import isqrt
import json
import random


def is_prime(p):
    return p >= 2 and all(p % q for q in range(2, isqrt(p) + 1))


def elementary(values, t):
    if t < 0:
        return 0
    return sum(prod_term(items) for items in combinations(values, t))


def prod_term(values):
    ans = 1
    for v in values:
        ans *= v
    return ans


def evaluate(coeff, x, p):
    ans = 0
    for c in reversed(coeff):
        ans = (ans * x + c) % p
    return ans


def interpolate(points, p):
    out = [0] * len(points)
    for i, (x, y) in enumerate(points):
        coeff = [1]
        den = 1
        for j, (z, _) in enumerate(points):
            if i == j:
                continue
            nxt = [0] * (len(coeff) + 1)
            for a, c in enumerate(coeff):
                nxt[a] = (nxt[a] - z * c) % p
                nxt[a + 1] = (nxt[a + 1] + c) % p
            coeff = nxt
            den = den * (x - z) % p
        fac = y * pow(den, -1, p) % p
        out = [(a + fac * b) % p for a, b in zip(out, coeff)]
    return tuple(out)


def greedy_lists(sizes, t, p):
    assert is_prime(p)
    order = sorted(range(len(sizes)), key=sizes.__getitem__)
    lists = {}
    forbidden_counts = []
    for i in order:
        forbidden = set()
        for anchors in combinations(lists, t):
            for values in product(*(lists[j] for j in anchors)):
                poly = interpolate(list(zip(anchors, values)), p)
                forbidden.add(evaluate(poly, i, p))
        allowed = [v for v in range(p) if v not in forbidden]
        assert len(allowed) >= sizes[i]
        lists[i] = allowed[:sizes[i]]
        forbidden_counts.append(len(forbidden))
    return [lists[i] for i in range(len(sizes))], forbidden_counts


def all_interpolants(lists, t, p):
    out = []
    for anchors in combinations(range(len(lists)), t):
        for values in product(*(lists[i] for i in anchors)):
            out.append((anchors, interpolate(list(zip(anchors, values)), p)))
    assert len({poly for _, poly in out}) == len(out)
    for anchors, poly in out:
        meets = [i for i, values in enumerate(lists)
                 if evaluate(poly, i, p) in values]
        assert meets == list(anchors)
    return out


def bilinear(coeff, h, y, p):
    a, b, c, d = coeff
    return (a + b * h + c * y + d * h * y) % p


def grid(interpolants, n, r, p):
    return [(nu * n + j, y, evaluate(poly, y, p))
            for nu, (_, poly) in enumerate(interpolants)
            for j in range(n) for y in range(r, p)]


def uncovered(data, candidates, p):
    return sum(not any(bilinear(f, h, y, p) == z for f in candidates)
               for h, y, z in data)


def lower(T, n, r, p, M, d=1, t=2):
    return max(T-M, 0) * max(n-d*M, 0) * max(p-r-(t-1)*M, 0)


def main():
    certificate = {}
    generic_cases = [([2], 1, 17), ([1, 2], 1, 17),
                     ([2, 3], 2, 53), ([2, 2, 2], 2, 211),
                     ([1, 2, 2, 1], 3, 211), ([1, 1, 1, 1], 2, 53)]
    records = []
    for sizes, t, p in generic_cases:
        lists, forb = greedy_lists(sizes, t, p)
        polys = all_interpolants(lists, t, p)
        assert len(polys) == elementary(sizes, t)
        records.append(dict(sizes=sizes, t=t, p=p, lists=lists,
                            forbidden_counts=forb, candidates=len(polys)))
    certificate['generic_lists'] = records

    order_cases = 0
    for r in range(1, 6):
        for sizes in combinations_with_replacement(range(1, 4), r):
            for t in range(1, r+1):
                D = sizes[-1]-1 + elementary(sizes[:-1], t)
                scores = [max(vals[i]-1+elementary(vals[:i], t)
                              for i in range(r)) for vals in set(permutations(sizes))]
                assert min(scores) == D
                order_cases += 1
    certificate['greedy_order_exact_cases'] = order_cases

    p, r, n = 13, 2, 2
    lists, _ = greedy_lists([1, 2], 2, p)
    polys = all_interpolants(lists, 2, p)
    data = grid(polys, n, r, p)
    T = len(polys)
    bound = lower(T, n, r, p, 1)
    minimum = len(data)
    minimizing_candidate = None
    checks = 0
    for f in product(range(p), repeat=4):
        loss = uncovered(data, [f], p)
        assert loss >= bound
        if loss < minimum:
            minimum, minimizing_candidate = loss, f
        checks += 1
    target_cover = [(poly[0], 0, poly[1], 0) for _, poly in polys]
    assert uncovered(data, target_cover, p) == 0
    certificate['exhaustive_single_candidate'] = dict(
        p=p, sizes=[1, 2], n=n, grid_points=len(data), candidates_tested=checks,
        proved_bound=bound, exact_minimum_uncovered=minimum,
        minimizing_candidate=minimizing_candidate, exact_cover_size=T)

    rng = random.Random(20261007)
    p, r, n = 53, 4, 6
    lists, _ = greedy_lists([1]*r, 2, p)
    polys = all_interpolants(lists, 2, p)
    data = grid(polys, n, r, p)
    targets = [(poly[0], 0, poly[1], 0) for _, poly in polys]
    random_checks = 0
    for M in range(len(polys)):
        for trial in range(20):
            cand = [tuple(rng.randrange(p) for _ in range(4)) for _ in range(M)]
            if trial % 2:
                for j in range(M):
                    if rng.randrange(2):
                        cand[j] = targets[rng.randrange(len(targets))]
            assert uncovered(data, cand, p) >= lower(len(polys), n, r, p, M)
            random_checks += 1
    certificate['seeded_multi_candidate_cases'] = random_checks

    small_r_checks = 0
    for u, v in product(range(13), repeat=2):
        matches = sum((u+v*h) % 13 == (0 if h < 2 else 1) for h in range(4))
        assert matches < 4
        small_r_checks += 1
    certificate['below_threshold_univariate_candidates'] = small_r_checks
    certificate['status'] = 'all exact checks passed'
    destination = Path(__file__).with_name('interpolation_certificate.json')
    destination.write_text(json.dumps(certificate, indent=2)+'\n')
    print(json.dumps(certificate, indent=2))


if __name__ == '__main__':
    main()
