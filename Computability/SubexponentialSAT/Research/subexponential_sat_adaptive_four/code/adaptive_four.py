#!/usr/bin/env python3
"""Exact cached tensor contraction using an adaptive four-block merge.

This is a finite demonstration of the regrouping and paid-oracle interface.
Its matrix backend is ordinary cubic multiplication, NOT a realization of
the asymptotic fast matrix-multiplication algorithm used in the proof.

There is one index for every ordered pair (g, h), g != h. An index is read
by both endpoint factors. Missing entries in ``domains`` have cardinality 1.
The oracle is called once for each assignment to each factor's incident
indices. For a vertex g the incident-index order is ``Network.incident(g)``.
All arithmetic in factor values takes place in the supplied commutative ring.
"""
from dataclasses import dataclass, field
from itertools import product
from math import prod
from typing import Any, Callable, Dict, FrozenSet, List, Mapping, Tuple

Edge = Tuple[int, int]
Index = Tuple[int, ...]
Oracle = Callable[[int, Index], Any]


@dataclass(frozen=True)
class ModRing:
    modulus: int

    def __post_init__(self):
        if self.modulus < 2:
            raise ValueError("modulus must be at least two")

    @property
    def zero(self):
        return 0

    @property
    def one(self):
        return 1

    def add(self, a, b):
        return (a + b) % self.modulus

    def mul(self, a, b):
        return (a * b) % self.modulus


@dataclass(frozen=True)
class DualRing:
    """Pairs a + b*epsilon over Z/modulus, with epsilon**2 = 0."""

    modulus: int

    def __post_init__(self):
        if self.modulus < 2:
            raise ValueError("modulus must be at least two")

    @property
    def zero(self):
        return (0, 0)

    @property
    def one(self):
        return (1, 0)

    def add(self, a, b):
        return ((a[0] + b[0]) % self.modulus,
                (a[1] + b[1]) % self.modulus)

    def mul(self, a, b):
        return ((a[0] * b[0]) % self.modulus,
                (a[0] * b[1] + a[1] * b[0]) % self.modulus)


@dataclass
class Network:
    order: int
    domains: Mapping[Edge, int]
    edges: Tuple[Edge, ...] = field(init=False)
    sizes: Dict[Edge, int] = field(init=False)

    def __post_init__(self):
        if self.order not in (4, 8, 12):
            raise ValueError("this demonstration supports 4, 8, or 12 factors")
        self.edges = tuple((g, h) for g in range(self.order)
                           for h in range(self.order) if g != h)
        allowed = set(self.edges)
        if any(edge not in allowed for edge in self.domains):
            raise ValueError("invalid ordered-pair index")
        if any(type(size) is not int or size < 1 for size in self.domains.values()):
            raise ValueError("index cardinalities must be positive integers")
        self.sizes = {edge: self.domains.get(edge, 1) for edge in self.edges}

    def incident(self, vertex):
        return tuple(edge for edge in self.edges if vertex in edge)

    def boundary(self, vertices):
        return tuple(edge for edge in self.edges
                     if (edge[0] in vertices) != (edge[1] in vertices))

    def assignments(self, axes):
        return product(*(range(self.sizes[edge]) for edge in axes))

    def cardinality(self, axes):
        return prod(self.sizes[edge] for edge in axes)


@dataclass
class BlockTable:
    vertices: FrozenSet[int]
    axes: Tuple[Edge, ...]
    values: Dict[Index, Any]


@dataclass
class Ledger:
    oracle_calls: List[int]
    matrix_shapes: List[Tuple[int, int, int]] = field(default_factory=list)
    ring_additions: int = 0
    ring_multiplications: int = 0
    largest_single_table: int = 0
    matching_candidates: List[Dict[str, Any]] = field(default_factory=list)
    selected_matching: Any = None

    def summary(self):
        return {
            "oracle_calls_per_factor": self.oracle_calls,
            "oracle_calls_total": sum(self.oracle_calls),
            "matrix_shapes": self.matrix_shapes,
            "ring_additions": self.ring_additions,
            "ring_multiplications": self.ring_multiplications,
            "largest_single_table_entries": self.largest_single_table,
            "matching_candidates": self.matching_candidates,
            "selected_matching": self.selected_matching,
            "matrix_backend": "naive exact cubic; no fast-backend runtime claim",
            "selection_cost_model": "rectangular exponent 12/5, compared by exact fifth powers",
        }


def merge_axes(network, left, right):
    if left.vertices & right.vertices:
        raise ValueError("merged vertex sets must be disjoint")
    shared_set = set(left.axes) & set(right.axes)
    shared = tuple(edge for edge in network.edges if edge in shared_set)
    outside_left = tuple(edge for edge in left.axes if edge not in shared_set)
    outside_right = tuple(edge for edge in right.axes if edge not in shared_set)
    return outside_left, shared, outside_right


def merge_shape(network, left, right):
    return tuple(network.cardinality(axes) for axes in merge_axes(network, left, right))


def fast_cost_fifth_power(shape):
    """Exact fifth power of d1*d2*d3/min(d1,d2,d3)**(3/5)."""
    d1, d2, d3 = shape
    smallest = min(shape)
    numerator = (d1 * d2 * d3) ** 5
    denominator = smallest ** 3
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise ArithmeticError("dimension cost was unexpectedly nonintegral")
    return quotient


def merge_tables(network, ring, left, right, ledger):
    """Reshape two boundary tables, multiply naively, and restore axis order."""
    left_axes, shared_axes, right_axes = merge_axes(network, left, right)
    left_keys = tuple(network.assignments(left_axes))
    shared_keys = tuple(network.assignments(shared_axes))
    right_keys = tuple(network.assignments(right_axes))
    shape = (len(left_keys), len(shared_keys), len(right_keys))
    ledger.matrix_shapes.append(shape)

    def lookup(table, axes_a, key_a, axes_b, key_b):
        assignment = dict(zip(axes_a, key_a))
        assignment.update(zip(axes_b, key_b))
        return table.values[tuple(assignment[edge] for edge in table.axes)]

    matrix_a = [[lookup(left, left_axes, x, shared_axes, y)
                 for y in shared_keys] for x in left_keys]
    matrix_b = [[lookup(right, shared_axes, y, right_axes, z)
                 for z in right_keys] for y in shared_keys]
    result_vertices = left.vertices | right.vertices
    result_axes = network.boundary(result_vertices)
    values = {}
    for i, x in enumerate(left_keys):
        for k, z in enumerate(right_keys):
            total = ring.zero
            for j in range(len(shared_keys)):
                term = ring.mul(matrix_a[i][j], matrix_b[j][k])
                total = ring.add(total, term)
                ledger.ring_multiplications += 1
                ledger.ring_additions += 1
            assignment = dict(zip(left_axes, x))
            assignment.update(zip(right_axes, z))
            key = tuple(assignment[edge] for edge in result_axes)
            values[key] = total
    if len(values) != network.cardinality(result_axes):
        raise ArithmeticError("output table has the wrong cardinality")
    ledger.largest_single_table = max(ledger.largest_single_table, len(values))
    return BlockTable(result_vertices, result_axes, values)


def cached_adaptive_four(network, ring, oracle):
    """Return the exact contraction and a paid-oracle/operation ledger."""
    ledger = Ledger([0] * network.order)
    singletons = {}
    for vertex in range(network.order):
        axes = network.incident(vertex)
        values = {}
        for key in network.assignments(axes):
            values[key] = oracle(vertex, key)
            ledger.oracle_calls[vertex] += 1
        ledger.largest_single_table = max(ledger.largest_single_table, len(values))
        singletons[vertex] = BlockTable(frozenset((vertex,)), axes, values)

    def build(vertices):
        if len(vertices) == 1:
            return singletons[vertices[0]]
        half = len(vertices) // 2
        left = build(vertices[:half])
        right = build(vertices[half:])
        return merge_tables(network, ring, left, right, ledger)

    size = network.order // 4
    blocks = [build(tuple(range(j * size, (j + 1) * size))) for j in range(4)]
    matchings = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
    best = None
    for matching in matchings:
        shapes = [merge_shape(network, blocks[a], blocks[b]) for a, b in matching]
        cost = max(fast_cost_fifth_power(shape) for shape in shapes)
        ledger.matching_candidates.append({
            "matching": matching,
            "merge_shapes": shapes,
            "max_cost_fifth_power": cost,
        })
        if best is None or cost < best[0]:
            best = (cost, matching)
    ledger.selected_matching = best[1]
    (a, b), (c, d) = best[1]
    left = merge_tables(network, ring, blocks[a], blocks[b], ledger)
    right = merge_tables(network, ring, blocks[c], blocks[d], ledger)
    scalar = merge_tables(network, ring, left, right, ledger)
    if scalar.axes or set(scalar.values) != {()}:
        raise ArithmeticError("final table is not a scalar")
    return scalar.values[()], ledger


def brute_force(network, ring, oracle):
    """Independent full assignment sum, deliberately without table regrouping."""
    positions = {edge: i for i, edge in enumerate(network.edges)}
    projections = [[positions[edge] for edge in network.incident(vertex)]
                   for vertex in range(network.order)]
    total = ring.zero
    for assignment in network.assignments(network.edges):
        term = ring.one
        for vertex, projection in enumerate(projections):
            key = tuple(assignment[i] for i in projection)
            term = ring.mul(term, oracle(vertex, key))
        total = ring.add(total, term)
    return total
