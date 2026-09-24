#!/usr/bin/env python3
"""Finite diagnostics for Proposition 1, NOT a Turing-degree computation.

Standard library only; compatible with Python 3.9 and later.
The exhaustive checks below neither prove nor refute the open C5 realization.
The article gives the elementary general argument independently of this code.
"""
from itertools import combinations, product
from pathlib import Path
import json


def edge(u: int, v: int) -> tuple:
    return tuple(sorted((u, v)))


def is_transitive(relation: set, vertices: range) -> bool:
    return all((u, w) in relation
               for u in vertices for v in vertices for w in vertices
               if (u, v) in relation and (v, w) in relation)


def main() -> None:
    vertices = range(5)
    pairs = list(combinations(vertices, 2))
    cycle = {edge(i, (i + 1) % 5) for i in vertices}
    cycle_edges = sorted(cycle)
    transitive_count = 0
    for directions in product((0, 1), repeat=5):
        relation = {(v, u) if flip else (u, v)
                    for (u, v), flip in zip(cycle_edges, directions)}
        if is_transitive(relation, vertices):
            transitive_count += 1

    # Scale distances by 2 to make every operation exact integer arithmetic.
    # Any graph has distances 0 on the diagonal, 2 on edges, 1 otherwise.
    metric_count = 0
    for bits in product((0, 1), repeat=len(pairs)):
        edges = {p for p, bit in zip(pairs, bits) if bit}
        distance = [[0 if i == j else 2 if edge(i, j) in edges else 1
                     for j in vertices] for i in vertices]
        if not all(distance[i][j] <= distance[i][k] + distance[k][j]
                   for i in vertices for j in vertices for k in vertices):
            raise AssertionError("Unexpected triangle-inequality failure")
        metric_count += 1

    complement = set(pairs) - cycle
    permuted_cycle = {edge((2 * u) % 5, (2 * v) % 5) for u, v in cycle}
    if transitive_count != 0:
        raise AssertionError("Unexpected transitive orientation of C5")
    if permuted_cycle != complement:
        raise AssertionError("Unexpected failure of complement relabeling")

    result = {
        "scope": "Finite graph checks only; no oracle computations or Lean proof",
        "C5_orientations_checked": 32,
        "C5_transitive_orientations": transitive_count,
        "five_vertex_binary_distance_metrics_checked": metric_count,
        "C5_complement_isomorphic_via_i_to_2i_mod_5": True,
        "open_C5_Turing_degree_realization_status": "not resolved by this experiment"
    }
    output = json.dumps(result, indent=2)
    print(output)
    Path(__file__).with_name("finite_checks_results.json").write_text(
        output + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
