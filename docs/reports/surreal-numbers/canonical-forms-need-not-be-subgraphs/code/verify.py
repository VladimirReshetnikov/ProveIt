#!/usr/bin/env python3
"""Reproduce the finite checks in the accompanying article.

Run with Python 3.10 or newer. No third-party packages are used.
An exception or a failed assertion makes the process exit unsuccessfully.
These exact-arithmetic tests supplement, but do not replace, the proofs.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

from surreal_forms import (Forms, birthday, denominator_exponent,
                           enumerate_forms, has_subgraph, prefix_path,
                           prefix_values)


def born_on(day: int) -> list[Q]:
    """Independently list the values whose intrinsic birthday is day."""
    if day == 0:
        return [Q(0)]
    result = [Q(-day), Q(day)]
    for k in range(1, day):
        ceiling = day - k
        scale = 1 << k
        for numerator in range((ceiling - 1) * scale + 1, ceiling * scale, 2):
            x = Q(numerator, scale)
            result.extend((-x, x))
    return sorted(result)


def independent_value(left: list[Q], right: list[Q], rank: int) -> Q:
    """Search by birthday, not by the evaluator's denominator algorithm."""
    for day in range(rank + 1):
        candidates = [x for x in born_on(day)
                      if all(a < x for a in left) and all(x < b for b in right)]
        if candidates:
            assert len(candidates) == 1, "The simplest value was not unique"
            return candidates[0]
    raise AssertionError("No cut value found within the form's rank")


def spanning_canonical(arena: Forms, root: int) -> bool:
    """Check the stronger, side- and value-preserving spanning statement."""
    vertices = arena.closure(root)
    by_value = {arena.nodes[v].value: v for v in vertices}
    if len(by_value) != len(vertices):
        return False
    canonical = arena.canonical(arena.nodes[root].value)
    if len(arena.closure(canonical)) != len(vertices):
        return False
    for v in arena.closure(canonical):
        c = arena.nodes[v]
        if c.value not in by_value:
            return False
        a = arena.nodes[by_value[c.value]]
        for canonical_side, actual_side in ((c.left, a.left), (c.right, a.right)):
            actual = {arena.nodes[u].value for u in actual_side}
            if not {arena.nodes[u].value for u in canonical_side} <= actual:
                return False
    return True


def run(output: Path, bound: int) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    arena = Forms()
    o = arena.zero
    p = arena.canonical(1)
    n = arena.canonical(-1)
    z = arena.make((n,), ())
    half = arena.make((z,), (p,))
    assert arena.stats(half) == {"value": "1/2", "rank": 3, "vertices": 5,
                                 "edges": 5, "cycle_rank": 1, "girth": 5}
    assert not has_subgraph(arena.adjacency(arena.canonical(Q(1, 2))),
                            arena.adjacency(half))
    zero_prime = arena.make((), (p,))
    h = arena.canonical(Q(1, 2))
    quarter = arena.make((zero_prime,), (h,))
    assert arena.nodes[quarter].value == Q(1, 4)
    assert arena.nodes[quarter].rank == birthday(Q(1, 4)) == 3
    assert not has_subgraph(arena.adjacency(arena.canonical(Q(1, 4))),
                            arena.adjacency(quarter))
    named = {"pentagon_half": arena.certificate(half),
             "minimum_rank_quarter": arena.certificate(quarter)}
    (output / "named_certificates.json").write_text(json.dumps(named, indent=2) + "\n")

    odd_rows = []
    for m in range(1, 21):
        root = arena.odd_cycle_half(m)
        stats = arena.stats(root)
        assert stats == {"value": "1/2", "rank": 2*m + 1, "vertices": 2*m + 3,
                         "edges": 2*m + 3, "cycle_rank": 1, "girth": 2*m + 3}
        odd_rows.append({"m": m, **stats})
    write_csv(output / "odd_cycles.csv", odd_rows)

    finite = enumerate_forms(arena, bound)
    counts = []
    failures = []
    minimal_counts: Counter[Q] = Counter()
    independently_checked: set[int] = set()
    edge_minimizers = 0
    for size in range(1, bound + 1):
        failures_this_size = 0
        for root in sorted(finite[size]):
            x = arena.nodes[root].value
            b, k = birthday(x), denominator_exponent(x)
            stats = arena.stats(root)
            assert stats["vertices"] == size
            assert size >= b + 1
            assert stats["cycle_rank"] >= k
            assert stats["edges"] >= b + k
            assert arena.nodes[root].rank >= b
            path = prefix_path(arena, root)
            assert len(path) == len(set(path))
            for a, child in zip(path, path[1:]):
                assert child in arena.nodes[a].left + arena.nodes[a].right
            values = [arena.nodes[v].value for v in path]
            position = 0
            for target in reversed(prefix_values(arena, x)):
                position = values.index(target, position) + 1
            if size == b + 1:
                minimal_counts[x] += 1
                assert spanning_canonical(arena, root)
            if stats["edges"] == b + k:
                edge_minimizers += 1
                assert root == arena.canonical(x)
            canonical_graph = arena.adjacency(arena.canonical(x))
            if not has_subgraph(canonical_graph, arena.adjacency(root)):
                failures_this_size += 1
                failures.append(arena.certificate(root))
            for v in arena.closure(root) - independently_checked:
                node = arena.nodes[v]
                independent = independent_value(
                    [arena.nodes[u].value for u in node.left],
                    [arena.nodes[u].value for u in node.right], node.rank)
                assert node.value == independent
                independently_checked.add(v)
        counts.append({"vertices": size, "forms": len(finite[size]),
                       "canonical_subgraph_failures": failures_this_size})
    expected = [1, 2, 10, 123, 3724]
    if bound <= 5:
        assert [row["forms"] for row in counts] == expected[:bound]
        assert [row["canonical_subgraph_failures"] for row in counts] == [0,0,0,0,16][:bound]
    minimal_rows = []
    for day in range(bound):
        for x in born_on(day):
            b, k = birthday(x), denominator_exponent(x)
            predicted = 1 << (b*(b-1)//2 - k)
            assert minimal_counts[x] == predicted
            minimal_rows.append({"value": str(x), "birthday": b,
                                 "denominator_exponent": k,
                                 "minimum_vertices": b+1,
                                 "minimum_edges": b+k,
                                 "predicted_forms": predicted,
                                 "observed_forms": minimal_counts[x]})
    write_csv(output / "exhaustive_counts.csv", counts)
    write_csv(output / "node_minimal_counts.csv", minimal_rows)
    (output / "all_small_counterexamples.json").write_text(
        json.dumps(failures, indent=2) + "\n")

    fibonacci = [0, 1]
    for _ in range(14):
        fibonacci.append(fibonacci[-1] + fibonacci[-2])

    @lru_cache(maxsize=None)
    def leaf_count(node_id: int) -> int:
        node = arena.nodes[node_id]
        return (sum(leaf_count(v) for v in node.left + node.right)
                if node.left or node.right else 1)

    fibonacci_rows = []
    for k in range(13):
        values = ([Q(0)] if k == 0 else
                  [Q(m, 1 << k) for m in range(1, 1 << k, 2)])
        maximum = max(leaf_count(arena.canonical(x)) for x in values)
        assert maximum == fibonacci[k+2]
        fibonacci_rows.append({"denominator_exponent": k,
                               "values_checked_in_unit_interval": len(values),
                               "maximum_leaves": maximum,
                               "predicted_fibonacci": fibonacci[k+2]})
    write_csv(output / "fibonacci_leaf_bounds.csv", fibonacci_rows)

    high_rows = []
    for day in range(6):
        for x in born_on(day):
            for spacing in (4, 6):
                root, meta = arena.high_girth(x, spacing)
                stats = arena.stats(root)
                leaves, internal = meta["leaves"], meta["internal"]
                assert leaves <= fibonacci[denominator_exponent(x)+2]
                assert internal <= birthday(x) * leaves
                assert arena.nodes[root].value == x
                assert stats["vertices"] == internal + 2*spacing*(leaves-1) + 1
                assert stats["edges"] == internal + leaves - 1 + 2*spacing*(leaves-1)
                assert stats["cycle_rank"] == leaves - 1
                assert stats["rank"] == 2*spacing*(leaves-1) + meta["last_leaf_depth"]
                assert stats["girth"] is None or stats["girth"] >= 2*spacing + 2
                if denominator_exponent(x):
                    assert stats["girth"] is not None
                    # The canonical graph has a triangle; a high-girth host has none.
                    assert stats["girth"] > 3
                high_rows.append({**stats, **meta})
    write_csv(output / "high_girth_examples.csv", high_rows)

    summary = {"python_version": platform.python_version(), "vertex_bound": bound,
               "total_forms": sum(row["forms"] for row in counts),
               "counts_by_size": counts,
               "canonical_subgraph_failures": len(failures),
               "independent_cut_evaluations": len(independently_checked),
               "edge_minimizers_checked": edge_minimizers,
               "node_minimal_value_classes_checked": len(minimal_rows),
               "odd_cycle_instances_checked": len(odd_rows),
               "high_girth_instances_checked": len(high_rows),
               "fibonacci_maximum_exponents_checked": len(fibonacci_rows),
               "fibonacci_value_instances_checked": sum(
                   row["values_checked_in_unit_interval"] for row in fibonacci_rows),
               "all_assertions_passed": True,
               "scope": "Exact finite checks; not a formal proof or a novelty certificate."}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    text = ["EXACT FINITE VERIFICATION", "", json.dumps(summary, indent=2), "",
            "All prefix-path, vertex, edge, cycle-rank, node-minimal enumeration,",
            "canonical spanning, unique edge-minimizer, odd-cycle, and high-girth",
            "assertions passed. Values in the exhaustive small-form experiment",
            "were also checked by an independent birthday-enumeration evaluator.",
            "", "The mathematical proofs, not these tests, establish the infinite families."]
    (output / "verification.txt").write_text("\n".join(text) + "\n")
    return summary


def write_csv(path: Path, rows: list[dict]) -> None:
    if not rows:
        return
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results")
    parser.add_argument("--bound", type=int, choices=range(1, 6), default=5)
    args = parser.parse_args()
    print(json.dumps(run(args.output, args.bound), indent=2))


if __name__ == "__main__":
    main()
