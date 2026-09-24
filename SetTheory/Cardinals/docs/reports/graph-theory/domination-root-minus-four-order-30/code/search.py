#!/usr/bin/env python3
"""Reproducible exact search for the one-hub, bare-corner C4 construction.

Enumerates rooted trees through a chosen order, retains realizable ratios
B/(A+B) with C(-4)=0, closes under forest products within the size budget,
and solves 21 + c + r*(a+b) = 0 by exact rational arithmetic.

This is NOT an exhaustive search over all graphs of a given order.
Python 3.10+; no external packages or precomputed cache required.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from pathlib import Path
from time import perf_counter


def shape_text(shape: tuple) -> str:
    return '(' + ''.join(shape_text(child) for child in shape) + ')'


def catalogue(maximum: int):
    sizes = {(): 1}
    states = {(): (-4, 0, 1)}
    counts = {'1': 1}
    levels = {1: [()]}
    for n in range(2, maximum + 1):
        pool = sorted(sizes, key=lambda t: (sizes[t], t))
        def multisets(remaining, start=0):
            if remaining == 0:
                yield ()
                return
            for j in range(start, len(pool)):
                tree = pool[j]
                size = sizes[tree]
                if size > remaining:
                    break
                for rest in multisets(remaining - size, j):
                    yield (tree,) + rest
        levels[n] = list(multisets(n - 1))
        counts[str(n)] = len(levels[n])
        for tree in levels[n]:
            sizes[tree] = n
            all_states = root_dominated = roots_absent = 1
            for child in tree:
                a, b, c = states[child]
                all_states *= a + b + c
                root_dominated *= a + b
                roots_absent *= b
            states[tree] = (-4 * all_states, root_dominated - roots_absent, roots_absent)
    single = {}
    for n, trees in levels.items():
        for tree in trees:
            a, b, c = states[tree]
            if c == 0 and a + b:
                q = Fraction(b, a + b)
                single.setdefault(q, tree)
    minimal = {Fraction(1): (0, ())}
    by_cost = {0: {Fraction(1): ()}}
    base = {n: [] for n in range(2, maximum + 1)}
    for q, tree in single.items():
        base[sizes[tree]].append((q, tree))
    for n in range(2, maximum + 1):
        fresh = {}
        for m in range(2, n + 1):
            for q, tree in base[m]:
                for r, forest in by_cost.get(n - m, {}).items():
                    product = q * r
                    if product not in minimal and product not in fresh:
                        fresh[product] = forest + (tree,)
        by_cost[n] = fresh
        minimal.update({q: (n, trees) for q, trees in fresh.items()})
    return minimal, counts, len(single)


def graph_from_hit(m: int, forests: list[tuple]) -> dict:
    edges = [(0, 1), (1, 2), (2, 3), (3, 0)]
    count = 4
    def add_tree(shape):
        nonlocal count
        root = count
        count += 1
        for child in shape:
            child_root = add_tree(child)
            edges.append((root, child_root))
        return root
    hub = add_tree(((),) * m)
    edges += [(1, hub), (2, hub)]
    for site, forest in zip((1, 2, 3), forests):
        for tree in forest:
            root = add_tree(tree)
            edges.append((site, root))
    return {'order': count, 'edges': edges, 'root': -4}


def run(maximum: int, initial_bound: int, max_leaves: int) -> dict:
    from domination import core_polynomial, evaluate
    start = perf_counter()
    cat, tree_counts, single_count = catalogue(maximum)
    arr = sorted((n, q, trees) for q, (n, trees) in cat.items())
    best = initial_bound
    queries = 0
    hits = []
    # Try the five-leaf hub first, then the other permitted hub sizes.
    for m in sorted(range(1, max_leaves + 1), key=lambda m: (m != 5, m)):
        r = Fraction(4 ** (m - 1), 4 ** (m - 1) - 3 ** m)
        rn, rd = r.numerator, r.denominator
        base = 5 + m
        for i, (na, a, ta) in enumerate(arr):
            if base + 2 * na >= best:
                break
            an, ad = a.numerator, a.denominator
            for nb, b, tb in arr[i:]:
                if base + na + nb >= best:
                    break
                bn, bd = b.numerator, b.denominator
                c = Fraction(-21 * rd * ad * bd - rn * (an * bd + bn * ad),
                             rd * ad * bd)
                queries += 1
                if c not in cat:
                    continue
                nc, tc = cat[c]
                n = base + na + nb + nc
                if n >= best:
                    continue
                graph = graph_from_hit(m, [ta, tb, tc])
                polynomial, _ = core_polynomial(graph['order'], graph['edges'])
                if evaluate(polynomial, -4) != 0 or graph['order'] != n:
                    raise RuntimeError('Search hit failed independent graph verification')
                best = n
                graph['coefficients'] = polynomial
                hit = {'order': n, 'hub_leaves': m,
                       'site_ratios': list(map(str, (a, b, c))),
                       'site_shapes': [[shape_text(t) for t in forest]
                                       for forest in (ta, tb, tc)],
                       'graph': graph}
                hits.append(hit)
                print(f'HIT: order={n}; m={m}; ratios={hit["site_ratios"]}', flush=True)
    return {'root': -4, 'tree_order_limit': maximum, 'initial_strict_bound': initial_bound,
            'maximum_hub_leaves': max_leaves, 'tree_counts': tree_counts,
            'single_tree_ratios': single_count, 'forest_ratios': len(cat),
            'rational_queries': queries, 'best_order': best, 'hits': hits,
            'seconds': round(perf_counter() - start, 3),
            'scope': 'One bare C4 corner; one star hub; site forests with <= limit vertices each.'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=14)
    parser.add_argument('--bound', type=int, default=33)
    parser.add_argument('--max-leaves', type=int, default=15)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'results/search.json')
    args = parser.parse_args()
    if not 2 <= args.limit <= 16 or args.bound < 6 or args.max_leaves < 1:
        parser.error('Require 2 <= limit <= 16, bound >= 6, max-leaves >= 1')
    result = run(args.limit, args.bound, args.max_leaves)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'hits'}, indent=2))


if __name__ == '__main__':
    main()
