#!/usr/bin/env python3
"""Reproduce deterministic exact checks. Run: python verify.py --full.

--quick: all naturally labelled posets to n=4, signatures to n=8,
         layered words over {1,2,3} of length at most 6.
--full:  corresponding limits 6, 15, and 9; also 30 seeded SP samples.
The JSON report and certificates are written to --output (default: results).
"""
from __future__ import annotations
import argparse
import json
import platform
import random
import time
from itertools import product
from pathlib import Path
from simplex_posets import (NEG, LEAF, STATES, KAPPA, Invariants, combine,
    series_matrix, evaluate, layered_expr, layered_formula, natural_posets,
    decompose, geometric_check, from_expr, maximum_clique)


def safe_json(obj):
    if isinstance(obj, float) and obj == NEG:
        return '-infinity'
    if isinstance(obj, dict):
        return {str(k): safe_json(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [safe_json(v) for v in obj]
    return obj


def check_potential(inv):
    tau = inv.avoiding_origin-inv.order_simplex
    assert inv.n-3*tau >= KAPPA[inv.state-1]
    assert inv.height <= inv.order_simplex <= inv.chain_simplex
    assert inv.gap <= max(0, (inv.n-2)//3)
    if tau < 0:
        assert tau == -1 and inv.state == 1 and inv.height == inv.order_simplex


def transition_certificate():
    table = []
    for a, b in product(range(8), repeat=2):
        m = series_matrix(STATES[a], STATES[b])
        delta = int(max(m))
        assert delta in (0, 1)
        out = STATES.index(tuple(x-delta for x in m))
        allowance = KAPPA[a]+KAPPA[b]-3+3*delta
        assert KAPPA[out] <= allowance
        table.append({'left': a+1, 'right': b+1, 'output': out+1,
                      'delta': delta, 'potential_slack': allowance-KAPPA[out]})
    return table


def signatures(limit):
    levels = {1: {Invariants(1, LEAF, 1, 0)}}
    rows = []
    for n in range(1, limit+1):
        if n > 1:
            current = set()
            for a in range(1, n):
                for x in levels[a]:
                    for y in levels[n-a]:
                        for op in ('S', 'P'):
                            current.add(combine(op, x, y))
            levels[n] = current
        for inv in levels[n]:
            check_potential(inv)
        rows.append({'n': n, 'distinct_signatures': len(levels[n]),
                     'maximum_gap': max(x.gap for x in levels[n])})
        print('signatures', rows[-1], flush=True)
    return rows


def exact_geometry(limit):
    rows = []
    for n in range(1, limit+1):
        total = sp_count = pairs = certificates = 0
        for p in natural_posets(n):
            total += 1
            expr = decompose(p)
            if expr is None:
                continue
            sp_count += 1
            inv = evaluate(expr)
            check_potential(inv)
            order = geometric_check(p, 'O')
            chain = geometric_check(p, 'C')
            assert tuple(order['values']) == inv.matrix, (p, expr, order, inv)
            assert chain['values'] == [inv.height, inv.avoiding_origin]
            pairs += order['pair_checks']+chain['pair_checks']
            certificates += sum(w is not None for w in order['witnesses']+chain['witnesses'])
        rows.append({'n': n, 'naturally_labelled_posets': total,
                     'series_parallel_posets': sp_count,
                     'pair_face_tests': pairs, 'simplex_face_certificates': certificates})
        print('geometry', rows[-1], flush=True)
    return rows


def random_expr(n, rng):
    if n == 1:
        return 'x'
    k = rng.randrange(1, n)
    return (rng.choice(('S', 'P')), random_expr(k, rng), random_expr(n-k, rng))


def random_geometry():
    rng = random.Random(20260920)
    checks = pairs = 0
    for n in (7, 8, 9):
        for _ in range(10):
            expr = random_expr(n, rng)
            inv = evaluate(expr)
            check_potential(inv)
            p = from_expr(expr)
            order, chain = geometric_check(p, 'O'), geometric_check(p, 'C')
            assert tuple(order['values']) == inv.matrix
            assert chain['values'] == [inv.height, inv.avoiding_origin]
            pairs += order['pair_checks']+chain['pair_checks']
            checks += 1
    return {'seed': 20260920, 'samples': checks, 'sizes': [7, 8, 9],
            'pair_face_tests': pairs}


def layers(limit):
    rows = []
    for r in range(1, limit+1):
        count = 0
        for sizes in product((1, 2, 3), repeat=r):
            inv = evaluate(layered_expr(sizes))
            so, sc, _ = layered_formula(sizes)
            assert (so, sc) == (inv.order_simplex, inv.chain_simplex)
            count += 1
        rows.append({'length': r, 'words_checked': count})
    print('layered words', sum(r['words_checked'] for r in rows), flush=True)
    return rows


def examples():
    result = []
    for sizes in ((2, 1, 2), (1, 2, 2), (2, 2), (2, 2, 2),
                  (3, 3, 3), (2, 1, 2, 1, 2)):
        expr = layered_expr(sizes)
        inv = evaluate(expr)
        p = from_expr(expr)
        result.append({'layers': sizes, 'n': inv.n, 'matrix': inv.matrix,
                       's_O': inv.order_simplex, 's_C': inv.chain_simplex,
                       'order_geometry': geometric_check(p, 'O'),
                       'chain_geometry': geometric_check(p, 'C')})
    for n in range(2, 101):
        g = (n-2)//3
        sizes = [1]*(n-(3*g+2)) + [2, 1]*g + [2]
        inv = evaluate(layered_expr(sizes))
        assert inv.n == n and inv.gap == g
    return result


def solver_unit_tests():
    """Compare clique optimization with subset enumeration, with constraints."""
    rng = random.Random(7312026)
    tests = 0
    for n in range(1, 11):
        for _ in range(25):
            adj = [0]*n
            for i in range(n):
                for j in range(i):
                    if rng.randrange(2):
                        adj[i] |= 1 << j
                        adj[j] |= 1 << i
            required = rng.randrange(1 << n)
            forbidden = rng.randrange(1 << n) & ~required
            expected = -1
            for mask in range(1 << n):
                if mask & required != required or mask & forbidden:
                    continue
                if all((mask & ~(1 << i)) & ~adj[i] == 0
                       for i in range(n) if mask >> i & 1):
                    expected = max(expected, mask.bit_count())
            actual = maximum_clique(adj, required, forbidden)
            assert (-1 if actual is None else actual.bit_count()) == expected
            tests += 1
    deep = 'x'
    for _ in range(4999):
        deep = ('S', deep, 'x')
    value = evaluate(deep)
    assert value.n == value.order_simplex == value.chain_simplex == 5000
    return {'brute_force_clique_comparisons': tests,
            'iterative_evaluator_chain_size': 5000}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--full', action='store_true')
    group.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path, default=Path('results'))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    table = transition_certificate()
    report = {'python': platform.python_version(), 'mode': 'full' if args.full else 'quick',
              'transition_cases': len(table)}
    report['unit_tests'] = solver_unit_tests()
    report['geometry'] = exact_geometry(6 if args.full else 4)
    report['random_geometry'] = random_geometry() if args.full else None
    report['signatures'] = signatures(15 if args.full else 8)
    report['layers'] = layers(9 if args.full else 6)
    witnesses = examples()
    report['extremizers_checked_through_n'] = 100
    report['elapsed_seconds'] = round(time.perf_counter()-start, 3)
    report['status'] = 'all checks passed'
    for name, value in [('verification.json', report), ('transitions.json', table),
                        ('examples.json', witnesses)]:
        (args.output/name).write_text(json.dumps(safe_json(value), indent=2)+'\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
