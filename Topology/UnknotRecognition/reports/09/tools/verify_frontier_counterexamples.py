#!/usr/bin/env python3
"""Reproduce the failure of a Catalan bound for arbitrary scan frontiers.

Run from this directory, or supply --fast-root to the directory containing
the fastunknot package.  This script is an exhaustive small-instance check,
not a knot recognizer.  It uses the repository's validated Diagram input
contract but computes each partial smoothing independently from scratch.

Output includes exact Laurent polynomials and their nonzero specializations
at the repository's actual Jones-filter field and evaluation point.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import Counter, defaultdict
from pathlib import Path
import sys


SMALL_PD = (
    (2, 3, 0, 4), (0, 5, 1, 6), (1, 7, 8, 2),
    (3, 9, 9, 8), (5, 10, 10, 7), (4, 11, 11, 6),
)

GREEDY_PD = (
    (2, 3, 0, 4), (0, 5, 1, 6), (1, 7, 8, 2),
    (13, 12, 3, 9), (9, 8, 10, 11), (11, 10, 12, 13),
    (18, 17, 5, 14), (14, 7, 15, 16), (16, 15, 17, 18),
    (23, 22, 4, 19), (19, 6, 20, 21), (21, 20, 22, 23),
)


def resolution(pd, prefix, bits):
    """Pairing and circle count of a full specified partial smoothing.

    Edge labels are vertices of an auxiliary graph.  Each smoothing supplies
    two graph edges.  A component has either two frontier ends or none.
    This construction does not call the incremental scanner or its caches.
    """
    labels = Counter(x for i in prefix for x in pd[i])
    frontier = {x for x, count in labels.items() if count == 1}
    parent = {x: x for x in labels}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i, bit in zip(prefix, bits):
        row = pd[i]
        pairs = ((0, 1), (2, 3)) if bit == 0 else ((0, 3), (1, 2))
        for a, b in pairs:
            parent[find(row[a])] = find(row[b])

    groups = defaultdict(list)
    for x in labels:
        groups[find(x)]
    for x in frontier:
        groups[find(x)].append(x)
    matching, circles = [], 0
    for ends in groups.values():
        if not ends:
            circles += 1
        elif len(ends) == 2:
            matching.append(tuple(sorted(ends)))
        else:
            raise AssertionError("a partial smoothing has invalid boundary degree")
    return tuple(sorted(matching)), circles, tuple(sorted(frontier))


def exact_prefix(pd, prefix, prime, point):
    """Enumerate 2^len(prefix) states and retain full Laurent coefficients."""
    polys = defaultdict(lambda: defaultdict(int))
    witnesses = {}
    p = len(prefix)
    for bits in itertools.product((0, 1), repeat=p):
        matching, loops, frontier = resolution(pd, prefix, bits)
        witnesses.setdefault(matching, bits)
        exponent = p - 2 * sum(bits)
        # A^(#0-#1) * delta^loops, delta = -A^2-A^(-2).
        for j in range(loops + 1):
            polys[matching][exponent + 4 * j - 2 * loops] += (
                (-1) ** loops * math.comb(loops, j)
            )
    nonzero = {}
    for matching, poly in polys.items():
        reduced = {e: c for e, c in poly.items() if c}
        if reduced:
            nonzero[matching] = reduced
    modular = {
        matching: sum(c * pow(point, e, prime) for e, c in poly.items()) % prime
        for matching, poly in nonzero.items()
    }
    modular = {m: value for m, value in modular.items() if value}
    width = len(frontier)
    k = width // 2
    return {
        "processed_crossings": list(prefix),
        "frontier_labels": frontier,
        "width": width,
        "catalan_disk_bound": math.comb(2 * k, k) // (k + 1),
        "unrestricted_matching_bound": math.prod(range(1, width, 2)),
        "distinct_geometric_matchings": len(witnesses),
        "nonzero_laurent_states": len(nonzero),
        "nonzero_modular_states": len(modular),
        "prime": prime,
        "A": point,
        "states": [
            {
                "matching": matching,
                "witness_smoothing_bits": witnesses[matching],
                "laurent_coefficient": [[e, c] for e, c in sorted(poly.items())],
                "modular_coefficient": modular.get(matching, 0),
            }
            for matching, poly in sorted(nonzero.items())
        ],
    }, modular


def incremental_prefix(pd, prefix, prime, point, glue):
    states = {(): 1}
    frontier = set()
    inverse = pow(point, -1, prime)
    delta = (-point * point - inverse * inverse) % prime
    for i in prefix:
        row = pd[i]
        for x in row:
            frontier.symmetric_difference_update([x])
        new = defaultdict(int)
        for matching, coefficient in states.items():
            for bit, weight in ((0, point), (1, inverse)):
                target, loops = glue(matching, row, bit, frontier)
                new[target] = (new[target] + coefficient * weight *
                               pow(delta, loops, prime)) % prime
        states = {m: c for m, c in new.items() if c}
    return states


def optimized_prefix(pd, prefix, prime, point, planar_class):
    """The actual Planar.glue path used by the Jones filter."""
    geometry = planar_class(shape_cache=False)
    states, frontier = {0: 1}, frozenset()
    inverse = pow(point, -1, prime)
    delta = (-point * point - inverse * inverse) % prime
    for i in prefix:
        geometry.stage(frontier, tuple(pd[i]))
        frontier = geometry.new_points()
        new = defaultdict(int)
        for matching, coefficient in states.items():
            for bit, weight in ((0, point), (1, inverse)):
                target, loops, _ = geometry.glue(matching, bit)
                new[target] = (new[target] + coefficient * weight *
                               pow(delta, loops, prime)) % prime
        states = {m: c for m, c in new.items() if c}
    return {geometry.pairs[m]: c for m, c in states.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    package_root = Path(__file__).resolve().parents[1]
    default_root = package_root / "fast"
    parser.add_argument("--fast-root", type=Path, default=default_root)
    parser.add_argument("--output", type=Path,
                        default=package_root / "data" / "frontier_counterexamples.json")
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast_root.resolve()))
    from fastunknot.diagram import Diagram
    from fastunknot.filters import PRIME, JONES_A, _glue
    from fastunknot.ordering import best_scan_order, scan_order
    from fastunknot.planar import Planar

    small = Diagram.from_pd(SMALL_PD)
    greedy = Diagram.from_pd(GREEDY_PD)
    assert scan_order(greedy.pd, start=0) == list(range(12))
    cases = [
        ("six_crossing_explicit_order", small, list(range(6)), 3),
        ("twelve_crossing_greedy_start_zero", greedy,
         scan_order(greedy.pd, start=0), 3),
    ]
    # This is a pre-existing repository fixture, not a constructed example.
    source = args.fast_root / "examples" / "conway_sum_2.json"
    conway = Diagram.from_json(json.loads(source.read_text()))
    order = best_scan_order(conway.pd, tries=min(conway.crossings, 12))
    cases.append(("existing_conway_sum_2_default_best_order", conway, order, 10))
    results = []
    for name, diagram, order, prefix_size in cases:
        summary, modular = exact_prefix(diagram.pd, order[:prefix_size], PRIME, JONES_A)
        incremental = incremental_prefix(diagram.pd, order[:prefix_size], PRIME, JONES_A, _glue)
        assert modular == incremental, (name, "independent and incremental scans differ")
        optimized = optimized_prefix(diagram.pd, order[:prefix_size], PRIME, JONES_A, Planar)
        assert modular == optimized, (name, "independent and optimized scans differ")
        assert summary["nonzero_modular_states"] > summary["catalan_disk_bound"], name
        summary.update({"name": name, "pd": diagram.pd, "complete_order": order,
                        "input_validation": "accepted by Diagram.from_pd: spherical, one component",
                        "independent_incremental_and_optimized_agree": True})
        results.append(summary)
        print(f"{name}: width {summary['width']}, geometric "
              f"{summary['distinct_geometric_matchings']}, Laurent "
              f"{summary['nonzero_laurent_states']}, modular "
              f"{summary['nonzero_modular_states']}, Catalan "
              f"{summary['catalan_disk_bound']}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"counterexamples": results}, indent=2) + "\n")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
