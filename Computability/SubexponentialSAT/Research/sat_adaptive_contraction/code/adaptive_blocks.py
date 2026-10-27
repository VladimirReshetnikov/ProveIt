"""Exact budget-adaptive three-block contraction for nine group factors.

This is a local mode-graph prototype, not a SAT solver.  A directed pair
index has a supplied finite dimension.  Each group factor reads only the
indices incident with that group.  The implementation caches the factors,
chooses a partition from the 280 partitions into three triples, constructs
the three boundary tables, and sums their product on crossing indices.

Python dictionaries realize convenient RAM tables.  The mathematical bit
model can instead use lexicographically ordered sequential records.
"""

from __future__ import annotations

from itertools import combinations, product
from math import prod
from typing import Callable, Mapping

Edge = tuple[int, int]
Partition = tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]
Factor = Callable[[int, Mapping[Edge, int]], int]


def triple_partitions() -> tuple[Partition, ...]:
    """All unlabeled partitions of {0,...,8} into three blocks of size 3."""
    result = []
    for tail in combinations(range(1, 9), 2):
        first = (0,) + tail
        rem = tuple(v for v in range(9) if v not in first)
        for middle_tail in combinations(rem[1:], 2):
            second = (rem[0],) + middle_tail
            third = tuple(v for v in rem if v not in second)
            result.append((first, second, third))
    return tuple(result)


PARTITIONS = triple_partitions()


def validate_dimensions(dimensions: Mapping[Edge, int], groups: int = 9) -> dict[Edge, int]:
    if type(groups) is not int or groups < 1:
        raise ValueError("The number of groups must be a positive integer")
    out = {}
    for edge, dim in dimensions.items():
        if (
            not isinstance(edge, tuple)
            or len(edge) != 2
            or any(type(v) is not int or not 0 <= v < groups for v in edge)
            or edge[0] == edge[1]
        ):
            raise ValueError("A pair index must join two distinct valid groups")
        if type(dim) is not int or dim < 0:
            raise ValueError("Dimensions must be nonnegative integers")
        out[edge] = dim
    return dict(sorted(out.items()))


def crossing_edges(partition: Partition, dimensions: Mapping[Edge, int]) -> tuple[Edge, ...]:
    block = {g: j for j, vertices in enumerate(partition) for g in vertices}
    return tuple(e for e in dimensions if block[e[0]] != block[e[1]])


def select_partition(dimensions: Mapping[Edge, int]) -> tuple[Partition, int]:
    """Minimize the exact crossing-domain product, without floating logs."""
    dimensions = validate_dimensions(dimensions)
    best = None
    best_cost = None
    for partition in PARTITIONS:
        cost = prod(dimensions[e] for e in crossing_edges(partition, dimensions))
        if best_cost is None or cost < best_cost:
            best, best_cost = partition, cost
    if best is None or best_cost is None:
        raise RuntimeError("The partition inventory was unexpectedly empty")
    return best, best_cost


def _assignments(edges: tuple[Edge, ...], dimensions: Mapping[Edge, int]):
    return product(*(range(dimensions[e]) for e in edges))


def direct_contract(dimensions: Mapping[Edge, int], factor: Factor, modulus: int | None = None,
                    groups: int = 9) -> int:
    """Reference literal sum over every pair-index assignment."""
    dimensions = validate_dimensions(dimensions, groups)
    if modulus is not None and (type(modulus) is not int or modulus < 1):
        raise ValueError("The modulus must be a positive integer")
    edges = tuple(dimensions)
    incidence = [tuple(e for e in edges if g in e) for g in range(groups)]
    total = 0
    for values in _assignments(edges, dimensions):
        assignment = dict(zip(edges, values))
        term = 1
        for g in range(groups):
            term *= factor(g, {e: assignment[e] for e in incidence[g]})
            if modulus is not None:
                term %= modulus
        total += term
        if modulus is not None:
            total %= modulus
    return total


def adaptive_contract(
    dimensions: Mapping[Edge, int], factor: Factor, modulus: int | None = None
) -> tuple[int, dict]:
    """Cache group functions, select a balanced partition, and contract it."""
    dimensions = validate_dimensions(dimensions)
    if modulus is not None and (type(modulus) is not int or modulus < 1):
        raise ValueError("The modulus must be a positive integer")
    stats = {"partitions_considered": len(PARTITIONS), "group_calls": 0,
             "table_assignments": 0, "table_entries": 0, "crossing_assignments": 0}
    if any(d == 0 for d in dimensions.values()):
        stats["empty_domain"] = True
        return 0, stats
    partition, cut_size = select_partition(dimensions)
    stats["partition"] = partition
    stats["crossing_domain_size"] = cut_size
    edges = tuple(dimensions)
    incidence = [tuple(e for e in edges if g in e) for g in range(9)]
    caches = []
    for g in range(9):
        cache = {}
        for values in _assignments(incidence[g], dimensions):
            value = factor(g, dict(zip(incidence[g], values)))
            cache[values] = value if modulus is None else value % modulus
            stats["group_calls"] += 1
        caches.append(cache)

    tables = []
    boundaries = []
    for block in partition:
        vertices = set(block)
        boundary = tuple(e for e in edges if (e[0] in vertices) != (e[1] in vertices))
        internal = tuple(e for e in edges if e[0] in vertices and e[1] in vertices)
        axes = boundary + internal
        positions = {e: j for j, e in enumerate(axes)}
        projected_positions = {g: tuple(positions[e] for e in incidence[g]) for g in block}
        table = {}
        for values in _assignments(axes, dimensions):
            stats["table_assignments"] += 1
            term = 1
            for g in block:
                term *= caches[g][tuple(values[j] for j in projected_positions[g])]
                if modulus is not None:
                    term %= modulus
            key = values[:len(boundary)]
            table[key] = table.get(key, 0) + term
            if modulus is not None:
                table[key] %= modulus
        stats["table_entries"] += len(table)
        tables.append(table)
        boundaries.append(boundary)

    cross = crossing_edges(partition, dimensions)
    cross_positions = {e: j for j, e in enumerate(cross)}
    projections = [tuple(cross_positions[e] for e in axes) for axes in boundaries]
    total = 0
    for values in _assignments(cross, dimensions):
        term = 1
        for table, projection in zip(tables, projections):
            term *= table[tuple(values[j] for j in projection)]
            if modulus is not None:
                term %= modulus
        total += term
        if modulus is not None:
            total %= modulus
        stats["crossing_assignments"] += 1
    return total, stats


def streaming_contract(
    dimensions: Mapping[Edge, int], factor: Factor, modulus: int | None = None,
    groups: int = 9,
) -> tuple[int, dict]:
    """Balanced binary contraction with no exponential table storage.

    At each split, enumerate only the directed pair indices between its two
    children. Sum their products; recurse independently within each child.
    A leaf reads the indices incident with its single group and calls the
    supplied expensive group factor. Only a constant-depth stack of indices
    and ring accumulators is stored when the group count is fixed.
    """
    dimensions = validate_dimensions(dimensions, groups)
    if modulus is not None and (type(modulus) is not int or modulus < 1):
        raise ValueError("The modulus must be a positive integer")
    stats = {"group_calls": 0, "cut_assignments": 0,
             "peak_assigned_indices": 0, "max_stack_depth": 0}
    if any(d == 0 for d in dimensions.values()):
        stats["empty_domain"] = True
        return 0, stats
    edges = tuple(dimensions)
    incidence = [tuple(e for e in edges if g in e) for g in range(groups)]

    def rec(vertices, assignment, depth):
        stats["max_stack_depth"] = max(stats["max_stack_depth"], depth)
        stats["peak_assigned_indices"] = max(stats["peak_assigned_indices"], len(assignment))
        if len(vertices) == 1:
            g = vertices[0]
            stats["group_calls"] += 1
            value = factor(g, {e: assignment[e] for e in incidence[g]})
            return value if modulus is None else value % modulus
        k = len(vertices)//2
        left, right = vertices[:k], vertices[k:]
        left_set, right_set = set(left), set(right)
        cut = tuple(e for e in edges if
                    (e[0] in left_set and e[1] in right_set) or
                    (e[1] in left_set and e[0] in right_set))
        total = 0
        for values in _assignments(cut, dimensions):
            stats["cut_assignments"] += 1
            for e, value in zip(cut, values):
                assignment[e] = value
            term = rec(left, assignment, depth+1) * rec(right, assignment, depth+1)
            total += term
            if modulus is not None:
                total %= modulus
        for e in cut:
            del assignment[e]
        return total

    value = rec(tuple(range(groups)), {}, 0)
    return value, stats


def stream_path_pairs(groups: int) -> int:
    """Maximum number of directed cut pairs on a balanced-tree leaf path."""
    if type(groups) is not int or groups < 1:
        raise ValueError("The number of groups must be positive")
    if groups == 1:
        return 0
    left, right = groups//2, groups-groups//2
    return 2*left*right + max(stream_path_pairs(left), stream_path_pairs(right))
