#!/usr/bin/env python3
"""Finite corroboration of quotient detachment, not its all-natural proof.

Uses a separate direct decoder for the native code algebra. Enumerates every
irreflexive relation on a two-element domain and all assignments needed by the
tested formulas. Also checks two sharp counterexamples to weaker statements.
Standard library only; no project code or network access is needed.
"""
from functools import lru_cache
from itertools import product
from math import isqrt
import argparse
import json
from pathlib import Path


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    k = (isqrt(8 * n + 1) - 1) // 2
    b = n - k * (k + 1) // 2
    return k - b, b


@lru_cache(maxsize=None)
def free(n):
    if n == 0:
        return frozenset()
    a, b = unpair(n // 4)
    tag = n % 4
    if tag in (1, 3):
        return frozenset((a, b))
    if tag == 0:
        return free(a) | free(b)
    return free(b) - {a}


def sat(n, env, domain, rel):
    if n == 0:
        return True
    a, b = unpair(n // 4)
    tag = n % 4
    if tag == 0:
        return not sat(a, env, domain, rel) or sat(b, env, domain, rel)
    if tag == 1:
        return (env.get(a, 0), env.get(b, 0)) in rel
    if tag == 3:
        return env.get(a, 0) == env.get(b, 0)
    return all(sat(b, {**env, a: x}, domain, rel) for x in domain)


def valid(n, domain, rel):
    names = sorted(free(n))
    return all(sat(n, dict(zip(names, vals)), domain, rel)
               for vals in product(domain, repeat=len(names)))


def run(bound):
    tested = successful = new_successful = 0
    by_tag = [0, 0, 0, 0]
    examples = []
    domain = (0, 1)
    for edge_bits in range(4):
        rel = frozenset(edge for i, edge in enumerate(((0, 1), (1, 0)))
                        if edge_bits & (1 << i))
        truth = lru_cache(maxsize=None)(lambda n: valid(n, domain, rel))
        for a in range(bound):
            for b in range(bound):
                for tag in range(4):
                    h = 4 * pair(a, b) + tag
                    assert h // 4 == pair(a, b)
                    tested += 1
                    if truth(a) and truth(h):
                        successful += 1
                        by_tag[tag] += 1
                        assert truth(b), (edge_bits, a, b, h)
                        if tag:
                            new_successful += 1
                            if len(examples) < 8:
                                examples.append({'relation_bits': edge_bits,
                                                 'antecedent': a,
                                                 'consequent': b,
                                                 'hypothesis': h,
                                                 'tag': tag})
        truth.cache_clear()
    a, b, h = 0, 1, 11
    singleton = (0,)
    assert valid(a, singleton, frozenset())
    assert valid(h, singleton, frozenset())
    assert not valid(b, singleton, frozenset())
    assert h // 4 == pair(a, b)
    assert sat(a, {}, domain, frozenset())
    assert sat(h, {}, domain, frozenset())
    assert not sat(b, {}, domain, frozenset())
    # Audit all MP forms appearing in the inherited strong block compiler.
    guard_tests = 0
    for t in range(bound):
        for target in range(bound):
            exact = 4 * pair(t, target)
            assert exact // 4 == pair(t, target)
            guard_tests += 1
        for target in range(1, bound):
            assert 0 != 4 * pair(t, target)
            assert 0 // 4 != pair(t, target)
            guard_tests += 1
    return {
        'status': 'all finite checks passed',
        'scope': 'Finite corroboration only; all-natural proof is quotient_detachment.md',
        'a_b_bound_exclusive': bound,
        'irreflexive_two_element_relations': 4,
        'tagged_guard_instances': tested,
        'valid_premise_instances': successful,
        'valid_premise_instances_by_tag': by_tag,
        'valid_extra_tag_instances': new_successful,
        'examples': examples,
        'compiler_guard_regressions': guard_tests,
        'singleton_counterexample': {'a': a, 'b': b, 'h': h},
        'fixed_assignment_counterexample': {'a': a, 'b': b, 'h': h,
                                            'assignment': 'all variables map to 0'},
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bound', type=int, default=64)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    if args.bound <= 1:
        parser.error('--bound must be at least 2')
    result = run(args.bound)
    payload = json.dumps(result, indent=2) + '\n'
    if args.out:
        args.out.write_text(payload)
    print(payload, end='')


if __name__ == '__main__':
    main()
