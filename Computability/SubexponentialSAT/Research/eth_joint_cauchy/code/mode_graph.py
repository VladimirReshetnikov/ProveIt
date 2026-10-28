#!/usr/bin/env python3
"""Generic exact contraction of a directed mode graph by three-block tables.

This is a small correctness prototype for the mode-aggregation identity.
It does not construct a SAT tensor network or implement the recursive SAT
solver. Edge index domains and group factors are supplied explicitly.

Every directed pair has its own index domain. A group factor sees precisely
the indices of pairs incident to that group. With a strict global weight
budget, exact per-pair weight allocations classify assignments once each.
For each allocation, internal indices are summed into boundary tables for
the blocks, and the remaining crossing indices are contracted literally.

Arithmetic is over the integers, or modulo an optional positive modulus.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from types import MappingProxyType
from typing import Callable, Iterator, Mapping, Sequence

Pair = tuple[int, int]


@dataclass(frozen=True, order=True)
class PairState:
    value: int
    weight: int = 0

    def __post_init__(self) -> None:
        if self.weight < 0:
            raise ValueError("state weights must be nonnegative")


Domains = Mapping[Pair, Sequence[PairState]]
Assignment = Mapping[Pair, PairState]
GroupFactor = Callable[[Assignment], int]


@dataclass
class ContractionStats:
    factor_evaluations: int = 0
    factor_lookups: int = 0
    cached_group_entries: int = 0
    allocations: int = 0
    table_entries: int = 0
    internal_assignments: int = 0
    crossing_assignments: int = 0
    literal_assignments: int = 0


def _validate(group_count: int, domains: Domains,
              factors: Sequence[GroupFactor], modulus: int | None) -> tuple[Pair, ...]:
    if group_count < 1 or len(factors) != group_count:
        raise ValueError("require one factor for every group")
    if modulus is not None and modulus < 1:
        raise ValueError("modulus must be positive")
    for (u, v), states in domains.items():
        if not (0 <= u < group_count and 0 <= v < group_count) or u == v:
            raise ValueError("a directed pair must join distinct valid groups")
        if any(not isinstance(state, PairState) for state in states):
            raise TypeError("domains must contain PairState objects")
        if len({state.value for state in states}) != len(states):
            raise ValueError("state values must be distinct within each pair domain")
    return tuple(sorted(domains))


def _assignments(pairs: Sequence[Pair], domains: Domains) -> Iterator[dict[Pair, PairState]]:
    for states in product(*(domains[pair] for pair in pairs)):
        yield dict(zip(pairs, states))


def _reduce(value: int, modulus: int | None) -> int:
    return value if modulus is None else value % modulus


def _factor_product(groups: Sequence[int], incident: Sequence[tuple[Pair, ...]],
                    assignment: Assignment, factors: Sequence[GroupFactor],
                    modulus: int | None, stats: ContractionStats,
                    cache: Sequence[Mapping[tuple[PairState, ...], int]] | None = None) -> int:
    value = 1
    for group in groups:
        if cache is not None:
            key = tuple(assignment[pair] for pair in incident[group])
            value = _reduce(value * cache[group][key], modulus)
            stats.factor_lookups += 1
            continue
        # No nonincident indices are exposed, even when the whole assignment
        # is available to the contraction scheduler.
        local = MappingProxyType({pair: assignment[pair] for pair in incident[group]})
        value = _reduce(value * factors[group](local), modulus)
        stats.factor_evaluations += 1
    return value


def literal_sum(group_count: int, domains: Domains, factors: Sequence[GroupFactor],
                *, weight_budget: int | None = None, modulus: int | None = None,
                stats: ContractionStats | None = None) -> int:
    """Enumerate all pair states, retaining total weight strictly below budget."""
    pairs = _validate(group_count, domains, factors, modulus)
    stats = stats if stats is not None else ContractionStats()
    incident = [tuple(pair for pair in pairs if group in pair) for group in range(group_count)]
    result = 0
    for assignment in _assignments(pairs, domains):
        if weight_budget is not None and sum(state.weight for state in assignment.values()) >= weight_budget:
            continue
        stats.literal_assignments += 1
        result += _factor_product(tuple(range(group_count)), incident, assignment,
                                  factors, modulus, stats)
        result = _reduce(result, modulus)
    return result


def exact_weight_allocations(pairs: Sequence[Pair], domains: Domains,
                             budget: int | None) -> Iterator[dict[Pair, tuple[PairState, ...]]]:
    """Classify global assignments by their exact pair weights, with no overlap."""
    if budget is None:
        if all(domains[pair] for pair in pairs):
            yield {pair: tuple(domains[pair]) for pair in pairs}
        return
    weights = [tuple(sorted({state.weight for state in domains[pair]})) for pair in pairs]
    for allocation in product(*weights):
        if sum(allocation) >= budget:
            continue
        yield {pair: tuple(state for state in domains[pair] if state.weight == weight)
               for pair, weight in zip(pairs, allocation)}


def blocked_sum(group_count: int, domains: Domains, factors: Sequence[GroupFactor],
                blocks: Sequence[Sequence[int]], *, weight_budget: int | None = None,
                modulus: int | None = None,
                stats: ContractionStats | None = None,
                cache_groups: bool = False, method: str = "direct") -> int:
    """Sum internal states into block tables, then contract crossing indices.

    Tables are rebuilt for each exact weight allocation. A directed pair
    appears once in the final crossing assignment and in both endpoint
    boundary-table keys. Internal pairs appear only in their own block.
    """
    pairs = _validate(group_count, domains, factors, modulus)
    blocks = tuple(tuple(block) for block in blocks)
    if method not in ("direct", "strassen"):
        raise ValueError("method must be direct or strassen")
    if method == "strassen" and len(blocks) != 3:
        raise ValueError("Strassen triangle contraction requires exactly three blocks")
    if any(not block for block in blocks):
        raise ValueError("blocks must be nonempty")
    if sorted(group for block in blocks for group in block) != list(range(group_count)):
        raise ValueError("blocks must partition the groups exactly once")
    stats = stats if stats is not None else ContractionStats()
    incident = [tuple(pair for pair in pairs if group in pair) for group in range(group_count)]
    owner = {group: b for b, block in enumerate(blocks) for group in block}
    crossing = tuple(pair for pair in pairs if owner[pair[0]] != owner[pair[1]])
    internal = [tuple(pair for pair in pairs if owner[pair[0]] == b == owner[pair[1]])
                for b in range(len(blocks))]
    boundary = [tuple(pair for pair in crossing if owner[pair[0]] == b or owner[pair[1]] == b)
                for b in range(len(blocks))]
    result = 0
    for allocated_domains in exact_weight_allocations(pairs, domains, weight_budget):
        stats.allocations += 1
        group_cache: list[dict[tuple[PairState, ...], int]] | None = None
        if cache_groups:
            group_cache = []
            for group in range(group_count):
                entries = {}
                for assignment in _assignments(incident[group], allocated_domains):
                    key = tuple(assignment[pair] for pair in incident[group])
                    entries[key] = _reduce(factors[group](MappingProxyType(assignment)), modulus)
                    stats.factor_evaluations += 1
                    stats.cached_group_entries += 1
                group_cache.append(entries)
        tables: list[dict[tuple[PairState, ...], int]] = []
        for b, block in enumerate(blocks):
            table: dict[tuple[PairState, ...], int] = {}
            for boundary_assignment in _assignments(boundary[b], allocated_domains):
                entry = 0
                for internal_assignment in _assignments(internal[b], allocated_domains):
                    assignment = boundary_assignment | internal_assignment
                    entry += _factor_product(block, incident, assignment, factors, modulus, stats, group_cache)
                    entry = _reduce(entry, modulus)
                    stats.internal_assignments += 1
                key = tuple(boundary_assignment[pair] for pair in boundary[b])
                table[key] = entry
                stats.table_entries += 1
            tables.append(table)
        if method == "strassen":
            cross_families = {
                (u, v): tuple(pair for pair in crossing
                              if {owner[pair[0]], owner[pair[1]]} == {u, v})
                for u, v in ((0, 1), (1, 2), (0, 2))}
            assignments01 = tuple(_assignments(cross_families[0, 1], allocated_domains))
            assignments12 = tuple(_assignments(cross_families[1, 2], allocated_domains))
            assignments20 = tuple(_assignments(cross_families[0, 2], allocated_domains))

            def lookup(block: int, left: Assignment, right: Assignment) -> int:
                assignment = dict(left) | dict(right)
                return tables[block][tuple(assignment[pair] for pair in boundary[block])]

            A = [[lookup(0, edge20, edge01) for edge01 in assignments01]
                 for edge20 in assignments20]
            B = [[lookup(1, edge01, edge12) for edge12 in assignments12]
                 for edge01 in assignments01]
            C = [[lookup(2, edge12, edge20) for edge20 in assignments20]
                 for edge12 in assignments12]
            result = _reduce(result + triangle_strassen(A, B, C, modulus=modulus), modulus)
            continue
        for assignment in _assignments(crossing, allocated_domains):
            term = 1
            for b, table in enumerate(tables):
                key = tuple(assignment[pair] for pair in boundary[b])
                term = _reduce(term * table[key], modulus)
            result = _reduce(result + term, modulus)
            stats.crossing_assignments += 1
    return result


def _matrix_add(A: list[list[int]], B: list[list[int]], modulus: int | None,
                sign: int = 1) -> list[list[int]]:
    return [[_reduce(a + sign * b, modulus) for a, b in zip(row_a, row_b)]
            for row_a, row_b in zip(A, B)]


def _square_strassen(A: list[list[int]], B: list[list[int]],
                     modulus: int | None) -> list[list[int]]:
    """Division-free seven-product recurrence for power-of-two square blocks."""
    n = len(A)
    if n == 1:
        return [[_reduce(A[0][0] * B[0][0], modulus)]]
    h = n // 2

    def split(X: list[list[int]]) -> tuple[list[list[int]], ...]:
        return ([row[:h] for row in X[:h]], [row[h:] for row in X[:h]],
                [row[:h] for row in X[h:]], [row[h:] for row in X[h:]])

    a, b, c, d = split(A)
    e, f, g, j = split(B)
    add = lambda X, Y: _matrix_add(X, Y, modulus)
    sub = lambda X, Y: _matrix_add(X, Y, modulus, -1)
    mul = lambda X, Y: _square_strassen(X, Y, modulus)
    p1 = mul(add(a, d), add(e, j))
    p2 = mul(add(c, d), e)
    p3 = mul(a, sub(f, j))
    p4 = mul(d, sub(g, e))
    p5 = mul(add(a, b), j)
    p6 = mul(sub(c, a), add(e, f))
    p7 = mul(sub(b, d), add(g, j))
    z00 = add(sub(add(p1, p4), p5), p7)
    z01 = add(p3, p5)
    z10 = add(p2, p4)
    z11 = add(sub(add(p1, p3), p2), p6)
    return [x + y for x, y in zip(z00, z01)] + [x + y for x, y in zip(z10, z11)]


def _matrix_shape(matrix: Sequence[Sequence[int]]) -> tuple[int, int]:
    if not matrix or not matrix[0] or any(len(row) != len(matrix[0]) for row in matrix):
        raise ValueError("matrices must be nonempty and rectangular")
    return len(matrix), len(matrix[0])


def rectangular_strassen(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]],
                         *, modulus: int | None = None) -> list[list[int]]:
    """Multiply m-by-k and k-by-n matrices using min-dimension square blocks.

    With d the largest power of two <=min(m,k,n), this takes
    O(ceil(m/d) ceil(k/d) ceil(n/d) d^log2(7)) ring operations.
    Padding is only to multiples of d, never to a common maximum dimension.
    """
    m, k = _matrix_shape(A)
    k2, n = _matrix_shape(B)
    if k != k2:
        raise ValueError("incompatible matrix dimensions")
    if modulus is not None and modulus < 1:
        raise ValueError("modulus must be positive")
    d = 1 << (min(m, k, n).bit_length() - 1)
    result = [[0 for _ in range(n)] for _ in range(m)]

    def block(X: Sequence[Sequence[int]], row: int, column: int,
              rows: int, columns: int) -> list[list[int]]:
        return [[_reduce(X[row + i][column + j], modulus)
                 if row + i < rows and column + j < columns else 0
                 for j in range(d)] for i in range(d)]

    for row in range(0, m, d):
        for column in range(0, n, d):
            for middle in range(0, k, d):
                product_block = _square_strassen(block(A, row, middle, m, k),
                                                 block(B, middle, column, k, n), modulus)
                for i in range(min(d, m - row)):
                    for j in range(min(d, n - column)):
                        result[row + i][column + j] = _reduce(
                            result[row + i][column + j] + product_block[i][j], modulus)
    return result


def triangle_strassen(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]],
                      C: Sequence[Sequence[int]], *, modulus: int | None = None) -> int:
    """Return trace(A B C) by rectangular Strassen and an entrywise contraction."""
    m, k = _matrix_shape(A)
    k2, n = _matrix_shape(B)
    n2, m2 = _matrix_shape(C)
    if (k, n, m) != (k2, n2, m2):
        raise ValueError("incompatible triangle dimensions")
    AB = rectangular_strassen(A, B, modulus=modulus)
    return _reduce(sum(AB[i][j] * C[j][i] for i in range(m) for j in range(n)), modulus)


def table_factor(incident_pairs: Sequence[Pair],
                 table: Mapping[tuple[int, ...], int]) -> GroupFactor:
    """Construct a factor from an explicit table indexed by incident values."""
    pairs = tuple(incident_pairs)
    data = dict(table)

    def factor(assignment: Assignment) -> int:
        if set(assignment) != set(pairs):
            raise ValueError("group received an incorrect incident-index set")
        return data[tuple(assignment[pair].value for pair in pairs)]

    return factor

