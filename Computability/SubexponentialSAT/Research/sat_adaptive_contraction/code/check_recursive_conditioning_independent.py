#!/usr/bin/env python3
"""Independent exact sum and call-accounting checks for uncached conditioning.

The ring is (Z/64)[V]/(V^2), which has zero divisors. Oracle values are
deterministic random tables only in this finite test; the algorithm receives
callables and performs no memoization.
"""
import itertools
import json
import math
from pathlib import Path
import random

MOD = 64


def add(x, y):
    return ((x[0]+y[0]) % MOD, (x[1]+y[1]) % MOD)


def mul(x, y):
    return ((x[0]*y[0]) % MOD, (x[0]*y[1]+x[1]*y[0]) % MOD)


def split(groups):
    k = len(groups)//2
    return groups[:k], groups[k:]


def cut(A, B):
    return tuple((a, b) for a in A for b in B)+tuple((b, a) for a in A for b in B)


def paths(groups, before=frozenset()):
    if len(groups) == 1:
        return {groups[0]: before}
    A, B = split(groups)
    current = frozenset(cut(A, B))
    if before & current:
        raise ArithmeticError('ancestor cuts overlap')
    return paths(A, before | current) | paths(B, before | current)


def condition(groups, domains, oracle):
    counts = {g: 0 for g in groups}
    context = {}
    max_context = 0
    if any(d == 0 for d in domains.values()):
        return (0, 0), counts, max_context

    def recurse(S):
        nonlocal max_context
        if len(S) == 1:
            g = S[0]
            counts[g] += 1
            return oracle(g, context)
        A, B = split(S)
        edges = cut(A, B)
        value = (0, 0)
        for values in itertools.product(*(range(domains[e]) for e in edges)):
            for e, v in zip(edges, values):
                context[e] = v
            max_context = max(max_context, len(context))
            left = recurse(A)
            right = recurse(B)
            value = add(value, mul(left, right))
            for e in edges:
                del context[e]
        return value

    return recurse(groups), counts, max_context


def literal(groups, domains, oracle):
    edges = tuple(domains)
    value = (0, 0)
    for values in itertools.product(*(range(domains[e]) for e in edges)):
        ctx = dict(zip(edges, values))
        term = (1, 0)
        for g in groups:
            term = mul(term, oracle(g, ctx))
        value = add(value, term)
    return value


def main():
    rng = random.Random(202610272)
    fixtures = []
    for r in range(2, 7):
        groups = tuple(range(r))
        edges = tuple((g, h) for g in groups for h in groups if g != h)
        for rep in range(8):
            domains = {e: 1 for e in edges}
            active = edges if r <= 4 and rep == 0 else rng.sample(edges, min(7, len(edges)))
            for e in active:
                domains[e] = rng.choice((2, 3)) if rep else 2
            if rep == 7:
                domains[edges[0]] = 0
            incident = {g: tuple(e for e in edges if g in e) for g in groups}
            tables = {}
            for g in groups:
                tables[g] = {
                    values: (rng.randrange(MOD), rng.randrange(MOD))
                    for values in itertools.product(*(range(domains[e]) for e in incident[g]))
                }

            def oracle(g, ctx):
                return tables[g][tuple(ctx[e] for e in incident[g])]

            actual, counts, peak = condition(groups, domains, oracle)
            expected = literal(groups, domains, oracle)
            if actual != expected:
                raise ArithmeticError(('wrong value', r, rep, actual, expected))
            path_sets = paths(groups)
            if all(domains.values()):
                expected_calls = {g: math.prod(domains[e] for e in path_sets[g]) for g in groups}
                if counts != expected_calls:
                    raise ArithmeticError(('wrong leaf-call ledger', r, rep, counts, expected_calls))
                if peak != max(map(len, path_sets.values())):
                    raise ArithmeticError('wrong peak assignment count')
            elif any(counts.values()):
                raise ArithmeticError('empty domain should avoid oracle calls')
            fixtures.append({'r': r, 'fixture': rep, 'result': actual,
                             'leaf_calls': sum(counts.values()),
                             'full_assignment_count': math.prod(domains.values()),
                             'peak_assigned_pairs': peak})
    cardinalities = {}
    for r in (2, 3, 4, 8, 9, 13, 16, 17):
        cardinalities[str(r)] = max(map(len, paths(tuple(range(r))).values()))
    if cardinalities['16'] != 170:
        raise ArithmeticError('wrong r=16 path cardinality')
    result = {'status': 'PASS', 'optimized_python': not __debug__,
              'ring': '(Z/64Z)[V]/(V^2)', 'fixture_count': len(fixtures),
              'exact_values_and_leaf_call_counts_agree': True,
              'path_cardinalities': cardinalities, 'fixtures': fixtures,
              'scope': 'Independent local sum-product and resource-accounting check; no SAT solver.'}
    suffix = '_optimized' if not __debug__ else ''
    (Path(__file__).resolve().parents[1] / 'results' / ('recursive_conditioning_independent'+suffix+'.json')).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'fixtures'}, indent=2))


if __name__ == '__main__':
    main()
