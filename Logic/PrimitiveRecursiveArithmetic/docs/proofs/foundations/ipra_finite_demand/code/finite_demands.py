#!/usr/bin/env python3
"""Exact finite checks for schedules and aggregate observations.

These are implementation checks, not an iPRA proof checker or an experiment
offered as evidence for the full universal mathematical statements.
"""
from fractions import Fraction as Q
from functools import lru_cache
import json


def dyadic(k):
    return Q(1, 2 ** k)


def schedule(demand, N, K):
    h = [K] * (N + 1)
    for n in range(N - 1, -1, -1):
        h[n] = demand(n, h[n + 1])
    return h


def compile_recursion(base, step, demand, N, K):
    h = schedule(demand, N, K)
    value = base(h[0])
    for n in range(N):
        value = step(n, h[n + 1], value)
    return value


def dist(x, y):
    assert len(x) == len(y)
    return max((abs(a - b) for a, b in zip(x, y)), default=Q(0))


def hausdorff(s, t):
    assert s and t
    return max(max(min(dist(x, y) for y in t) for x in s),
               max(min(dist(x, y) for x in s) for y in t))


def cover_check(s, t, eps):
    assert s and t and eps >= 0
    return (all(any(dist(x, y) <= eps for y in t) for x in s)
            and all(any(dist(x, y) <= eps for x in s) for y in t))


def nearest(q, s):
    assert s
    return min(s, key=lambda r: dist(q, r))


def chain(S, start, seed, length):
    q = S(start)[seed]
    output = [q]
    for j in range(length):
        q = nearest(q, S(start + j + 1))
        output.append(q)
    return output


LIMIT_SUPPORT = [(Q(0), Q(0)), (Q(1), Q(0)), (Q(0), Q(1))]


def aggregate(k):
    e = dyadic(k) / 8
    shift = e if k % 2 else -e
    values = [(x + shift, y - shift) for x, y in LIMIT_SUPPORT]
    if k % 3 == 0:
        values.append(values[0])  # Repeated entries must not alter the support.
    return list(reversed(values)) if k % 2 else values


def clip(q):
    return max(Q(0), min(Q(1), q))


def logistic(a, n, q):
    for _ in range(n):
        q = a * q * (1 - q)
    return q


def run_checks():
    counts = dict(nonmonotone_schedules=0, recursion_comparisons=0,
                  nonlinear_regularity_pairs=0, cover_reflections=0,
                  cover_triangles=0, chain_bounds=0,
                  approximate_optimization_cases=0)
    demands = [lambda n, k: k + 2,
               lambda n, k: (7 - k % 7) + n,
               lambda n, k: (k * k + 3 * n + 2) % 17]
    for D in demands:
        base = lambda k: k * k + 1
        step = lambda n, k, v: (n + 1) * v + k + 1

        @lru_cache(None)
        def direct(n, k):
            return base(k) if n == 0 else step(n - 1, k, direct(n - 1, D(n - 1, k)))

        for N in range(9):
            for K in range(11):
                h = schedule(D, N, K)
                assert h[N] == K
                assert all(h[n] == D(n, h[n + 1]) for n in range(N))
                counts['nonmonotone_schedules'] += 1
                assert compile_recursion(base, step, D, N, K) == direct(N, K)
                counts['recursion_comparisons'] += 1

    for a in (Q(0), Q(1, 2), Q(2), Q(4)):
        for x in (Q(0), Q(1, 4), Q(1, 2), Q(1)):
            def u(k):
                return x + (-1 if k % 2 else 1) * dyadic(k) / 3
            for N in range(6):
                values = [logistic(a, N, clip(u(k + 2 * N))) for k in range(5)]
                for k, vk in enumerate(values):
                    assert 0 <= vk <= 1
                    for ell, ve in enumerate(values):
                        assert abs(vk - ve) <= dyadic(k) + dyadic(ell)
                        counts['nonlinear_regularity_pairs'] += 1

    lists = [aggregate(k) for k in range(8)]
    for i, s in enumerate(lists):
        for j, t in enumerate(lists):
            h = hausdorff(s, t)
            assert h <= dyadic(i) + dyadic(j)
            assert cover_check(s, t, h)
            if h:
                assert not cover_check(s, t, h / 2)
            counts['cover_reflections'] += 1
            for u in lists:
                assert hausdorff(s, u) <= h + hausdorff(t, u)
                counts['cover_triangles'] += 1

    for start in range(6):
        for seed in range(len(aggregate(start))):
            values = chain(aggregate, start, seed, 12)
            for j in range(len(values)):
                assert values[j] in aggregate(start + j)
                for v in range(j, len(values)):
                    exact_sum = sum((dyadic(start + r) + dyadic(start + r + 1)
                                     for r in range(j, v)), Q(0))
                    assert dist(values[j], values[v]) <= exact_sum
                    assert exact_sum <= 3 * dyadic(start + j)
                    counts['chain_bounds'] += 1

    for a, b in [(Q(1), Q(2)), (Q(-3), Q(1, 2)), (Q(0), Q(0))]:
        L = abs(a) + abs(b)
        f = lambda q: a * q[0] + b * q[1]
        true_min = min(f(q) for q in LIMIT_SUPPORT)
        for s in range(8):
            values = aggregate(s)
            seed = min(range(len(values)), key=lambda i: f(values[i]))
            q = values[seed]
            witness_observations = chain(aggregate, s, seed, 12)
            # Compare with an independently known finite limiting support.
            for j, point in enumerate(witness_observations):
                assert f(point) <= true_min + (4 * L + 2) * dyadic(s)
                assert min(dist(point, p) for p in LIMIT_SUPPORT) <= dyadic(s + j) / 8
            counts['approximate_optimization_cases'] += 1

    return {"status": "passed", "scope": "Exact finite implementation checks only",
            "arithmetic": "fractions.Fraction", "counts": counts}


if __name__ == '__main__':
    print(json.dumps(run_checks(), indent=2))
