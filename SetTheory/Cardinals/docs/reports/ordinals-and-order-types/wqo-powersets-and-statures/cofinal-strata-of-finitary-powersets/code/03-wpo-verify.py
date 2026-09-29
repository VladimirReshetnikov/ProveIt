#!/usr/bin/env python3
"""Deterministic finite verification, not an infinite-order proof."""
from __future__ import annotations

from collections import Counter
from copy import deepcopy
from itertools import combinations, product
import json
from pathlib import Path
import platform
import random
import time

from frontier_heights import (
    CNF, ZERO, ONE, Poset, bits, downclosure, expand_limit_fibers,
    format_cnf, maximal_antichains, monomial, natural_sum, ordinal_add,
    parse_cnf, path_value, solve, solve_compressed, verify_certificate,
)

ROOT = Path(__file__).resolve().parents[1]
COUNTS: Counter = Counter()


def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(category)
    COUNTS[category] += 1


def naturally_labelled_posets(n: int):
    """Each transitive subrelation of 0<1<...<n-1, exactly once."""
    pairs = list(combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        succ = [0] * n
        for k, (i, j) in enumerate(pairs):
            if mask & (1 << k):
                succ[i] |= 1 << j
        if any(succ[j] & ~succ[i] for i in range(n) for j in bits(succ[i])):
            continue
        pred = [0] * n
        for i in range(n):
            for j in bits(succ[i]):
                pred[j] |= 1 << i
        yield Poset(n, tuple(pred), tuple(succ))


def independent_path(p: Poset, priorities, order) -> CNF:
    """Find each vertex's first later successor; group by retirement time.

    Does not use the profile frontier or path_value routines.
    """
    if not p.n:
        return ONE
    position = {v: i for i, v in enumerate(order)}
    groups = [[] for _ in range(p.n + 1)]
    for v in range(p.n):
        retirement = min((position[w] for w in bits(p.successors[v])), default=p.n)
        groups[retirement].append(priorities[v])
    result = ZERO
    for group in groups:
        if group:
            # Independently normalize a word of pure monomials by erasing
            # the strict lower-priority suffix before appending a term.
            e = max(group)
            seq = list(result)
            while seq and seq[-1][0] < e:
                seq.pop()
            if seq and seq[-1][0] == e:
                seq[-1] = (e, seq[-1][1] + 1)
            else:
                seq.append((e, 1))
            result = tuple(seq)
    return result


def finite_profile_checks(p: Poset) -> None:
    profiles = []
    for ideal in p.ideals():
        frontier = list(bits(p.frontier(ideal)))
        for coordinates in product(range(2), repeat=len(frontier)):
            values = dict(zip(frontier, coordinates))
            elements = frozenset((q, x) for q in bits(ideal)
                                 for x in range(values[q] + 1 if q in values else 4))
            profiles.append((ideal, values, elements))
    for i, a, da in profiles:
        for j, b, db in profiles:
            criterion = i & ~j == 0 and all(a[q] <= b[q] for q in a.keys() & b.keys())
            check(criterion == (da <= db), 'sampled_profile_inclusions')
    # Canonical maximal-antichain compression and edge weights.
    mas = set(maximal_antichains(p))
    for ideal in p.ideals():
        c = ideal & ~p.frontier(ideal)
        m = sum(1 << q for q in range(p.n)
                if not c & (1 << q) and p.predecessors[q] & ~c == 0)
        check(m in mas, 'canonical_frontier_membership')
        for v in range(p.n):
            if ideal & (1 << v) or p.predecessors[v] & ~ideal:
                continue
            j = ideal | (1 << v)
            d = j & ~p.frontier(j)
            m2 = sum(1 << q for q in range(p.n)
                     if not d & (1 << q) and p.predecessors[q] & ~d == 0)
            check((m & ~m2) == (p.frontier(ideal) & ~p.frontier(j)),
                  'compressed_retirement_identity')


def arithmetic_checks(rng: random.Random) -> None:
    for _ in range(20000):
        length = rng.randrange(1, 9)
        priorities = [rng.randrange(5) for _ in range(length - 1)] + [rng.randrange(1, 5)]
        lambdas = [monomial(p) if p else ZERO for p in priorities]
        gammas = []
        for i in range(length - 1):
            bound = max(priorities[i + 1:])
            gammas.append(tuple((e, c) for e in range(bound - 1, -1, -1)
                                if (c := rng.randrange(4)) > 0))
        gammas.append(ZERO)
        original = charged = ZERO
        for a, b in zip(lambdas, gammas):
            original = ordinal_add(original, natural_sum(a, b))
            charged = ordinal_add(charged, a)
        check(original == charged, 'deferred_absorption_cnf')


def main() -> None:
    start = time.perf_counter()
    rng = random.Random(24092026)
    census, weighted_instances, total_extensions = {}, 0, 0
    for n in range(7):
        posets = list(naturally_labelled_posets(n))
        census[str(n)] = len(posets)
        for index, p in enumerate(posets):
            uniform = solve(p, [1] * n)
            check(verify_certificate(uniform), 'uniform_certificates')
            compressed, chain = solve_compressed(p, [1] * n)
            check(parse_cnf(uniform['height_cnf']) == compressed, 'uniform_compression')
            if n:
                integer_ranks = {}
                for a in maximal_antichains(p):
                    da = downclosure(p, a)
                    integer_ranks[a] = 1 + max((integer_ranks[b] for b in integer_ranks
                                               if downclosure(p, b) & ~da == 0), default=0)
                longest = max(integer_ranks.values())
                check(compressed == ((1, longest),) and len(chain) == longest,
                      'uniform_maximal_antichain_height')
            if n <= 4:
                finite_profile_checks(p)
                assignments = product((1, 2, 3), repeat=n)
            elif n == 5:
                assignments = product((1, 3), repeat=n)
            elif index < 256:
                assignments = [tuple(rng.randrange(1, 5) for _ in range(n))]
            else:
                assignments = []
            orders = list(p.extensions()) if n <= 5 or (n == 6 and index < 256) else []
            for priorities in assignments:
                weighted_instances += 1
                answer = solve(p, priorities)
                value = parse_cnf(answer['height_cnf'])
                check(verify_certificate(answer), 'weighted_certificates')
                vals = [independent_path(p, priorities, order) for order in orders]
                total_extensions += len(vals)
                check(value == max(vals), 'dp_vs_all_extensions')
                check(value == solve_compressed(p, priorities)[0], 'weighted_compression')
                check(value == path_value(p, priorities, answer['linear_extension']), 'attaining_extension')
                if n:
                    bound = ZERO
                    for e in priorities:
                        bound = natural_sum(bound, monomial(e))
                    check(monomial(max(priorities)) <= value <= bound, 'budget_bounds')
                    check(sum(c for e, c in value) <= n, 'coefficient_budget')
                if weighted_instances % 41 == 0:
                    mapping = {e: 2 * e + 3 for e in set(priorities)}
                    remapped = tuple(mapping[e] for e in priorities)
                    remap_value = parse_cnf(solve(p, remapped)['height_cnf'])
                    expected = tuple((mapping[e], c) for e, c in value) if n else ONE
                    check(remap_value == expected, 'priority_chamber_invariance')
                    perm = list(range(n))
                    rng.shuffle(perm)
                    q = Poset.from_edges(n, [[perm[a], perm[b]] for a, b in p.edges()])
                    weights = [0] * n
                    for v in range(n):
                        weights[perm[v]] = priorities[v]
                    check(parse_cnf(solve(q, weights)['height_cnf']) == value, 'vertex_relabelling')
                    damaged = deepcopy(answer)
                    mode = weighted_instances % 5
                    if mode == 0:
                        damaged['height_cnf'] = [[9, 9]]
                    elif mode == 1:
                        damaged['states'][-1]['value'] = [[9, 9]]
                    elif mode == 2:
                        damaged['states'][-1]['frontier'] ^= 1
                    elif mode == 3:
                        damaged['states'][-1]['predecessor'] = [-1, -1]
                    else:
                        damaged['states'].pop()
                    try:
                        verify_certificate(damaged)
                    except ValueError:
                        check(True, 'tamper_rejections')
                    else:
                        raise AssertionError('tampered certificate accepted')
    arithmetic_checks(rng)
    examples = {
        'persistent_large_coordinate': {'n': 3, 'edges': [[1, 2]], 'priorities': [2, 1, 1]},
        'nonuniform_N': {'n': 4, 'edges': [[0, 2], [0, 3], [1, 3]], 'priorities': [3, 2, 1, 1]},
        'parallel_chains': {'n': 4, 'edges': [[0, 2], [1, 3]], 'priorities': [2, 3, 1, 1]},
        'height_two_overlap': {'n': 6, 'edges': [[0, 3], [0, 4], [1, 4], [1, 5], [2, 3], [2, 5]], 'priorities': [3, 2, 1, 1, 1, 1]},
        'transfinite_exponent_labels': {'n': 3, 'edges': [[1, 2]], 'priorities': [3, 1, 2], 'exponent_labels': {'1': 'omega', '2': 'omega+1', '3': 'epsilon_0'}},
    }
    outputs = {}
    for name, instance in examples.items():
        (ROOT / 'examples' / f'{name}.json').write_text(json.dumps(instance, indent=2) + '\n')
        p = Poset.from_edges(instance['n'], instance['edges'])
        result = solve(p, instance['priorities'])
        value, chain = solve_compressed(p, instance['priorities'])
        result['compressed_frontier_count'] = len(maximal_antichains(p))
        result['maximal_antichain_chain'] = [list(bits(m)) for m in chain]
        if 'exponent_labels' in instance:
            result['exponent_labels'] = instance['exponent_labels']
            result['height'] = format_cnf(value, instance['exponent_labels'])
        (ROOT / 'data' / f'{name}_certificate.json').write_text(json.dumps(result, indent=2) + '\n')
        outputs[name] = {key: value for key, value in result.items() if key != 'states'}
    limit_instance = {'n': 2, 'edges': [], 'fiber_cnfs': [[[2, 1], [1, 1]], [[1, 2]]]}
    (ROOT / 'examples' / 'limit_fibers.json').write_text(json.dumps(limit_instance, indent=2) + '\n')
    expanded, priorities, owners = expand_limit_fibers(Poset.from_edges(2, []), limit_instance['fiber_cnfs'])
    result = solve(expanded, priorities)
    result['expanded_block_owners'] = owners
    check(parse_cnf(result['height_cnf']) == ((2, 1), (1, 2)), 'limit_fiber_example')
    (ROOT / 'data' / 'limit_fibers_certificate.json').write_text(json.dumps(result, indent=2) + '\n')
    outputs['limit_fibers'] = {k: v for k, v in result.items() if k != 'states'}
    (ROOT / 'data' / 'examples_summary.json').write_text(json.dumps(outputs, indent=2) + '\n')
    report = {
        'status': 'all finite checks passed',
        'scope': 'Finite formulas, certificates, profiles, and CNF identities; not infinite-rank verification, Lean checking, or novelty certification.',
        'python': platform.python_version(), 'seed': 24092026,
        'naturally_labelled_posets_by_n': census,
        'weighted_instances': weighted_instances,
        'independently_valued_linear_extensions': total_extensions,
        'checks_by_category': dict(COUNTS), 'total_checks': sum(COUNTS.values()),
        'runtime_seconds': round(time.perf_counter() - start, 3),
    }
    (ROOT / 'data' / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
