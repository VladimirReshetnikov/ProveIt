#!/usr/bin/env python3
"""Independent finite algebra audit for an adaptive contraction-tree portfolio.

Ring: (Z/64Z)[V]/(V^2). Directed pair indices are kept separate in the
literal oracle and tensor contraction. The independent operation predictor
combines opposite directed dimensions on each undirected pair.

This checks regrouping, exact portfolio selection, child-factor caching,
and table-size accounting. Matrix multiplication is deliberately naive.
It is not a SAT solver or an implementation/test of a fast MM backend.
Only Python's standard library is required. Checks use explicit exceptions,
so running Python with -O does not disable them.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
from random import Random
from typing import Callable, Iterable


MODULUS = 64
Ring = tuple[int, int]
Axis = tuple[int, int]
ZERO: Ring = (0, 0)
ONE: Ring = (1, 0)


def add(x: Ring, y: Ring) -> Ring:
    return ((x[0] + y[0]) % MODULUS, (x[1] + y[1]) % MODULUS)


def mul(x: Ring, y: Ring) -> Ring:
    return (x[0] * y[0] % MODULUS, (x[0] * y[1] + x[1] * y[0]) % MODULUS)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def assignments(axes: tuple[Axis, ...], dimensions: dict[Axis, int]) -> Iterable[tuple[int, ...]]:
    return product(*(range(dimensions[axis]) for axis in axes))


def size(axes: Iterable[Axis], dimensions: dict[Axis, int]) -> int:
    return prod(dimensions[axis] for axis in axes)


@dataclass
class Table:
    name: str
    vertices: frozenset[int]
    axes: tuple[Axis, ...]
    values: dict[tuple[int, ...], Ring]
    cached_input: bool = False


class MemoryLedger:
    """Logical scalar-cell accounting, including still-live cached inputs."""

    def __init__(self) -> None:
        self.live: dict[str, int] = {}
        self.peak_live_cells = 0
        self.largest_table_cells = 0
        self.largest_new_table_cells = 0

    def allocate(self, name: str, cells: int, *, initial: bool = False) -> None:
        require(name not in self.live, f"Duplicate live table {name}")
        require(cells >= 1, "A dense table always has at least one cell")
        self.live[name] = cells
        self.peak_live_cells = max(self.peak_live_cells, sum(self.live.values()))
        self.largest_table_cells = max(self.largest_table_cells, cells)
        if not initial:
            self.largest_new_table_cells = max(self.largest_new_table_cells, cells)

    def release(self, table: Table) -> None:
        if not table.cached_input:
            require(table.name in self.live, f"Releasing absent table {table.name}")
            del self.live[table.name]


def fast_cost_power5(d1: int, d2: int, d3: int) -> int:
    """The exact fifth power of d1*d2*d3/min(d1,d2,d3)^(3/5)."""
    smallest = min(d1, d2, d3)
    numerator = (d1 * d2 * d3) ** 5
    denominator = smallest ** 3
    require(numerator % denominator == 0, "Cost fifth power must be integral")
    return numerator // denominator


def operation_dimensions(
    r: int, A: frozenset[int], B: frozenset[int], dimensions: dict[Axis, int]
) -> tuple[int, int, int]:
    """Predict dimensions independently, using coalesced undirected pairs."""
    require(A and B and A.isdisjoint(B), "Merge vertex sets must be disjoint and nonempty")
    outside = frozenset(range(r)) - A - B
    d1 = d2 = d3 = 1
    for g, h in combinations(range(r), 2):
        pair_size = dimensions.get((g, h), 1) * dimensions.get((h, g), 1)
        if (g in A and h in B) or (h in A and g in B):
            d2 *= pair_size
        elif (g in A and h in outside) or (h in A and g in outside):
            d1 *= pair_size
        elif (g in B and h in outside) or (h in B and g in outside):
            d3 *= pair_size
    return d1, d2, d3


def validate_tree(r: int, blocks: list[list[int]]) -> None:
    require(len(blocks) == 3 and all(blocks), "Top level must have three nonempty blocks")
    flattened = [v for block in blocks for v in block]
    require(sorted(flattened) == list(range(r)), "Tree must partition all vertices exactly once")


def predict_operations(r: int, blocks: list[list[int]], dimensions: dict[Axis, int]) -> list[dict]:
    validate_tree(r, blocks)
    operations: list[dict] = []

    def append(A: list[int], B: list[int], kind: str) -> None:
        d1, d2, d3 = operation_dimensions(r, frozenset(A), frozenset(B), dimensions)
        operations.append({
            "kind": kind,
            "left_vertices": sorted(A),
            "right_vertices": sorted(B),
            "matrix_dimensions": [d1, d2, d3],
            "cost_power5": fast_cost_power5(d1, d2, d3),
        })

    def visit(block: list[int]) -> None:
        if len(block) == 1:
            return
        split = len(block) // 2
        A, B = block[:split], block[split:]
        visit(A)
        visit(B)
        append(A, B, "block_merge")

    for block in blocks:
        visit(block)
    append(blocks[0], blocks[1], "triangle_product")
    require(len(operations) == r - 2, "Unexpected operation count")
    return operations


def select_tree(r: int, trees: list[list[list[int]]], dimensions: dict[Axis, int]) -> tuple[int, list[int]]:
    scores = [max(op["cost_power5"] for op in predict_operations(r, tree, dimensions)) for tree in trees]
    selected = min(range(len(trees)), key=lambda index: (scores[index], index))
    return selected, scores


def source_tables(r: int, dimensions: dict[Axis, int], seed: int, special: str = "") -> list[Table]:
    rng = Random(seed)
    active = sorted(axis for axis, dimension in dimensions.items() if dimension > 1)
    factors = []
    for vertex in range(r):
        axes = tuple(axis for axis in active if vertex in axis)
        values = {}
        for coordinates in assignments(axes, dimensions):
            # Signed inputs exercise the canonical ring residues too.
            value = (rng.randrange(-96, 97) % MODULUS, rng.randrange(-96, 97) % MODULUS)
            if not axes:
                # Isolated factors are units, avoiding accidental annihilation
                # of an otherwise informative fixture by many even constants.
                value = ((value[0] | 1) % MODULUS, value[1])
            if special == "zero" and vertex == 0:
                value = ZERO
            elif special == "nilpotent" and vertex == 0:
                value = (0, (rng.randrange(32) * 2 + 1) % MODULUS)
            elif special == "double_nilpotent" and vertex in (0, 1):
                value = (0, (rng.randrange(32) * 2 + 1) % MODULUS)
            values[coordinates] = value
        factors.append(Table(f"source_{vertex}", frozenset([vertex]), axes, values, True))
    return factors


def literal_contraction(factors: list[Table], dimensions: dict[Axis, int]) -> tuple[Ring, int]:
    """Independent literal sum over all original directed pair indices."""
    active = tuple(sorted(axis for axis, dimension in dimensions.items() if dimension > 1))
    locations = {axis: index for index, axis in enumerate(active)}
    projection = [[locations[axis] for axis in factor.axes] for factor in factors]
    total = ZERO
    count = 0
    for coordinates in assignments(active, dimensions):
        term = ONE
        for factor, positions in zip(factors, projection):
            key = tuple(coordinates[index] for index in positions)
            term = mul(term, factor.values[key])
        total = add(total, term)
        count += 1
    require(count == size(active, dimensions), "Literal assignment count is wrong")
    return total, count


def run_tree(
    r: int,
    blocks: list[list[int]],
    source: list[Table],
    dimensions: dict[Axis, int],
) -> tuple[Ring, dict]:
    validate_tree(r, blocks)
    tracker = MemoryLedger()
    caches = []
    child_calls = 0
    # Each queried group-function entry represents one child contraction call.
    # These fixtures supply its value explicitly; they do not implement the child SAT algorithm.
    for vertex, factor in enumerate(source):
        values = {}
        for coordinates in assignments(factor.axes, dimensions):
            child_calls += 1
            values[coordinates] = factor.values[coordinates]
        table = Table(f"cache_{vertex}", factor.vertices, factor.axes, values, True)
        tracker.allocate(table.name, len(values), initial=True)
        caches.append(table)
    expected_child_calls = sum(len(factor.values) for factor in source)
    require(child_calls == expected_child_calls, "Group-cache query count differs from the exact star sum")
    operations: list[dict] = []

    def merge(left: Table, right: Table, kind: str) -> Table:
        require(left.vertices.isdisjoint(right.vertices), "A merge repeats a vertex")
        shared = tuple(sorted(set(left.axes) & set(right.axes)))
        left_only = tuple(axis for axis in left.axes if axis not in shared)
        right_only = tuple(axis for axis in right.axes if axis not in shared)
        require(set(left_only).isdisjoint(right_only), "External index sets overlap")
        output_axes = tuple(sorted(left_only + right_only))
        d1, d2, d3 = size(left_only, dimensions), size(shared, dimensions), size(right_only, dimensions)
        output_cells = size(output_axes, dimensions)
        require(len(left.values) == d1 * d2, "Left matrix reshape changed cardinality")
        require(len(right.values) == d2 * d3, "Right matrix reshape changed cardinality")
        require(output_cells == d1 * d3, "Output matrix reshape changed cardinality")
        cost_power5 = fast_cost_power5(d1, d2, d3)
        for cells in [len(left.values), len(right.values), output_cells]:
            require(cost_power5 >= cells ** 5, "Fast-MM cost omitted an input/output table")
        name = f"table_{len(operations)}"
        tracker.allocate(name, output_cells)
        output_values: dict[tuple[int, ...], Ring] = {}
        ring_products = 0
        # Independently implement the reshaped matrix product by literal sum.
        # No claimed fast multiplication implementation is hidden here.
        for external_coordinates in assignments(output_axes, dimensions):
            external = dict(zip(output_axes, external_coordinates))
            total = ZERO
            for internal_coordinates in assignments(shared, dimensions):
                all_coordinates = dict(external)
                all_coordinates.update(zip(shared, internal_coordinates))
                left_key = tuple(all_coordinates[axis] for axis in left.axes)
                right_key = tuple(all_coordinates[axis] for axis in right.axes)
                total = add(total, mul(left.values[left_key], right.values[right_key]))
                ring_products += 1
            output_values[external_coordinates] = total
        require(ring_products == d1 * d2 * d3, "Naive matrix work count is wrong")
        operations.append({
            "kind": kind,
            "left_vertices": sorted(left.vertices),
            "right_vertices": sorted(right.vertices),
            "matrix_dimensions": [d1, d2, d3],
            "cost_power5": cost_power5,
            "left_cells": len(left.values),
            "right_cells": len(right.values),
            "output_cells": output_cells,
            "naive_ring_products": ring_products,
            "input_output_dominance_checks": 3,
        })
        tracker.release(left)
        tracker.release(right)
        return Table(name, left.vertices | right.vertices, output_axes, output_values)

    def build(block: list[int]) -> Table:
        if len(block) == 1:
            return caches[block[0]]
        split = len(block) // 2
        left = build(block[:split])
        right = build(block[split:])
        return merge(left, right, "block_merge")

    A, B, C = [build(block) for block in blocks]
    AB = merge(A, B, "triangle_product")
    require(set(AB.axes) == set(C.axes), "Triangle product and third block have different boundary axes")
    result = ZERO
    dot_products = 0
    for coordinates in assignments(AB.axes, dimensions):
        axis_values = dict(zip(AB.axes, coordinates))
        third_key = tuple(axis_values[axis] for axis in C.axes)
        result = add(result, mul(AB.values[coordinates], C.values[third_key]))
        dot_products += 1
    require(dot_products == len(AB.values) == len(C.values), "Triangle dot product has wrong size")
    require(operations[-1]["cost_power5"] >= dot_products ** 5, "Final dot product omitted from cost")
    tracker.release(AB)
    tracker.release(C)
    require(sum(tracker.live.values()) == expected_child_calls, "A temporary table was not released")
    predicted = predict_operations(r, blocks, dimensions)
    require(len(predicted) == len(operations), "Predictor and implementation operation counts differ")
    for index, (prediction, actual) in enumerate(zip(predicted, operations)):
        for key in ["kind", "left_vertices", "right_vertices", "matrix_dimensions", "cost_power5"]:
            require(prediction[key] == actual[key], f"Independent operation prediction failed at {index}: {key}")
    cost_power5 = max(operation["cost_power5"] for operation in operations)
    for factor in caches:
        require(cost_power5 >= len(factor.values) ** 5, "A cached group-function input escaped the operation cost")
    return result, {
        "input_child_calls": child_calls,
        "cache_cells": expected_child_calls,
        "largest_cached_table_cells": max(len(table.values) for table in caches),
        "peak_live_cells_including_cache": tracker.peak_live_cells,
        "largest_table_cells": tracker.largest_table_cells,
        "largest_new_table_cells": tracker.largest_new_table_cells,
        "operation_count": len(operations),
        "operation_input_output_checks": 3 * len(operations),
        "portfolio_score_power5": cost_power5,
        "naive_ring_products": sum(operation["naive_ring_products"] for operation in operations) + dot_products,
        "triangle_dot_products": dot_products,
        "operations": operations,
    }


def fixture_dimensions(r: int, style: int) -> dict[Axis, int]:
    if style == 0:
        arcs = [(0, 1), (1, 0), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0)]
    elif style == 1:
        arcs = [(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (2, 3), (3, 4), (4, 5), (5, 0)]
    elif style == 2:
        arcs = [(0, 1), (1, 0), (2, 3), (3, 2), (4, 5), (5, 6)]
    elif style == 3:
        arcs = []
    else:
        raise ValueError(style)
    require(all(max(axis) < r for axis in arcs), "Fixture uses a nonexistent vertex")
    # Several dimensions are 3, so list sizes need not be powers of two.
    return {axis: (3 if (index + style) % 3 == 0 else 2) for index, axis in enumerate(arcs)}


def run_fixture(
    name: str,
    r: int,
    trees: list[list[list[int]]],
    style: int,
    seed: int,
    special: str = "",
    supplied_dimensions: dict[Axis, int] | None = None,
) -> dict:
    dimensions = fixture_dimensions(r, style) if supplied_dimensions is None else supplied_dimensions
    factors = source_tables(r, dimensions, seed, special)
    oracle, assignments_count = literal_contraction(factors, dimensions)
    selected, scores = select_tree(r, trees, dimensions)
    tree_results = []
    for index, tree in enumerate(trees):
        answer, stats = run_tree(r, tree, factors, dimensions)
        require(answer == oracle, f"{name}: candidate {index} disagrees with the literal sum")
        require(stats["portfolio_score_power5"] == scores[index], "Selection score differs from actual operation ledger")
        tree_results.append({"candidate_index": index, "ring_result": list(answer), **stats})
    # Exercise the selected dispatch separately instead of merely reusing its tested result.
    dispatched_answer, dispatched_stats = run_tree(r, trees[selected], factors, dimensions)
    require(dispatched_answer == oracle, f"{name}: selected dispatch disagrees with literal sum")
    require(scores[selected] == min(scores), "Selected candidate does not minimize the exact score")
    require(dispatched_stats == {k: v for k, v in tree_results[selected].items() if k not in ("candidate_index", "ring_result")}, "Repeated selected dispatch has inconsistent accounting")
    if special in ("zero", "double_nilpotent"):
        require(oracle == ZERO, "Special ring fixture must vanish")
    if special == "nilpotent":
        require(oracle[0] == 0, "Nilpotent fixture has a nonzero constant coefficient")
    return {
        "name": name,
        "r": r,
        "active_directed_axes": [{"axis": list(axis), "dimension": dimension} for axis, dimension in sorted(dimensions.items())],
        "implicit_unit_directed_axes": r * (r - 1) - len(dimensions),
        "opposite_pairs_both_active": sum((h, g) in dimensions for g, h in dimensions if g < h),
        "literal_assignments": assignments_count,
        "literal_ring_result": list(oracle),
        "special": special,
        "selected_candidate": selected,
        "candidate_scores_power5": scores,
        "candidate_checks": tree_results,
        "selected_dispatch_checked_again": True,
    }


def run_checks(candidates_path: Path) -> dict:
    raw = candidates_path.read_bytes()
    candidates = json.loads(raw)
    portfolios = {}
    for r in (9, 13):
        key = f"({r}, 3)"
        require(key in candidates, f"Missing portfolio {key}")
        require(candidates[key]["r"] == r and len(candidates[key]["trees"]) == 3, "Malformed candidate portfolio")
        portfolios[r] = candidates[key]["trees"]
    expected_tail = [[0, 1, 2], [3, 4], [5, 6]]
    portfolios[7] = [expected_tail]
    require(portfolios[7] == [expected_tail], "The fixed tail partition is not the requested 3,2,2 tree")
    fixtures = []
    for r in (7, 9, 13):
        for style in (0, 1, 2):
            fixtures.append(run_fixture(f"r{r}_shape{style}", r, portfolios[r], style, seed=1000 * r + style))
    # Relabel the same asymmetric fixture to exercise every adaptive branch.
    # This also checks that the candidate's listed vertex order, rather than
    # a freshly sorted order, controls its internal floor/ceiling split.
    for r in (9, 13):
        for target in (1, 2):
            permutation = [vertex for block in portfolios[r][target] for vertex in block]
            relabeled = {
                (permutation[g], permutation[h]): dimension
                for (g, h), dimension in fixture_dimensions(r, 1).items()
            }
            fixture = run_fixture(
                f"r{r}_relabel_for_candidate{target}", r, portfolios[r], 1,
                seed=1000 * r + 20 + target, supplied_dimensions=relabeled,
            )
            require(fixture["selected_candidate"] == target, "Relabeled fixture failed to exercise the intended adaptive branch")
            fixtures.append(fixture)
    fixtures.append(run_fixture("r9_all_unit_axes", 9, portfolios[9], 3, 9009))
    fixtures.append(run_fixture("r13_zero_factor", 13, portfolios[13], 0, 13009, "zero"))
    fixtures.append(run_fixture("r9_nilpotent_factor", 9, portfolios[9], 1, 9010, "nilpotent"))
    fixtures.append(run_fixture("r7_double_nilpotent_factor", 7, portfolios[7], 2, 7011, "double_nilpotent"))
    all_runs = [run for fixture in fixtures for run in fixture["candidate_checks"]]
    return {
        "status": "PASS",
        "ring": "(Z/64Z)[V]/(V^2)",
        "scope": "exact finite algebra, adaptive selection, child-factor cache calls, and logical table sizes; no fast-MM backend or SAT solver",
        "candidate_file_sha256": hashlib.sha256(raw).hexdigest(),
        "portfolios_checked": {str(r): trees for r, trees in portfolios.items()},
        "fixture_count": len(fixtures),
        "candidate_tree_contractions": len(all_runs),
        "selected_dispatch_contractions": len(fixtures),
        "literal_assignments_total": sum(fixture["literal_assignments"] for fixture in fixtures),
        "operation_input_output_checks": sum(run["operation_input_output_checks"] for run in all_runs),
        "selected_candidate_distribution": {str(r): [sum(f["r"] == r and f["selected_candidate"] == i for f in fixtures) for i in range(len(trees))] for r, trees in portfolios.items()},
        "fixtures": fixtures,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidates", type=Path, default=Path(__file__).resolve().parents[1] / "data" / "adaptive_candidates.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run_checks(args.candidates)
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload, encoding="utf-8")
        print(json.dumps({key: result[key] for key in ["status", "fixture_count", "candidate_tree_contractions", "selected_dispatch_contractions", "literal_assignments_total", "operation_input_output_checks", "selected_candidate_distribution"]}, indent=2))
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
