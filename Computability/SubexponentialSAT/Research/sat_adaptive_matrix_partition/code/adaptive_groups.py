"""Exact prototype for the new nine-group aggregation step.

This is not a SAT solver.  Its table products use the classical scalar
backend, so it tests the finite identity, not the fast-matrix time bound.
Only Python's standard library is required.
"""
from dataclasses import dataclass
from itertools import combinations, product
from math import prod

VERTICES = tuple(range(9))
DIRECTED_PAIRS = tuple((i, j) for i in VERTICES for j in VERTICES if i != j)


def triple_partitions(vertices=VERTICES):
    """Yield each unordered partition into triples exactly once."""
    vertices = tuple(vertices)
    if not vertices:
        yield ()
        return
    first, rest = vertices[0], vertices[1:]
    for pair in combinations(rest, 2):
        block = (first,) + pair
        left = tuple(v for v in rest if v not in pair)
        for tail in triple_partitions(left):
            yield (block,) + tail


PARTITIONS = tuple(triple_partitions())


def select_partition(dimensions):
    """Minimize exact fifth-power matrix work, avoiding real logarithms.

For class dimensions A,B,C, the logarithmic objective is
log2(A*B*C) - 3/5*min(log2(A),log2(B),log2(C)).
The equivalent rational objective is (A*B*C)^5/min(A,B,C)^3.
"""
    if any(int(d) != d or d < 1 for d in dimensions.values()):
        raise ValueError("Every retained list must have a positive integer size")
    best = None
    for partition in PARTITIONS:
        block = {v: i for i, group in enumerate(partition) for v in group}
        sizes = [1, 1, 1]
        classes = {(0, 1): 0, (0, 2): 1, (1, 2): 2}
        for edge, dimension in dimensions.items():
            a, b = sorted((block[edge[0]], block[edge[1]]))
            if a != b:
                sizes[classes[a, b]] *= dimension
        numerator = prod(sizes) ** 5
        denominator = min(sizes) ** 3
        if best is None or numerator * best[2] < best[1] * denominator:
            best = partition, numerator, denominator, tuple(sizes)
    return best


class DualRing:
    """(Z/2^p Z)[V]/(V^2), including zero divisors and a nilpotent."""
    zero = (0, 0)
    one = (1, 0)

    def __init__(self, precision):
        if precision < 1:
            raise ValueError("positive precision required")
        self.modulus = 1 << precision

    def add(self, x, y):
        return ((x[0] + y[0]) % self.modulus,
                (x[1] + y[1]) % self.modulus)

    def mul(self, x, y):
        return ((x[0] * y[0]) % self.modulus,
                (x[0] * y[1] + x[1] * y[0]) % self.modulus)


@dataclass
class Table:
    vertices: frozenset
    edges: tuple
    data: dict


def assignments(edges, dimensions):
    for values in product(*(range(dimensions[e]) for e in edges)):
        yield dict(zip(edges, values))


def singleton_tables(dimensions, factor_entries, stats):
    """Cache the paid group functions; supplied entries stand for child calls."""
    tables = []
    active = tuple(sorted(e for e, d in dimensions.items() if d > 1))
    for v in VERTICES:
        incident = tuple(e for e in active if v in e)
        data = {}
        for assignment in assignments(incident, dimensions):
            key = tuple(assignment[e] for e in incident)
            data[key] = factor_entries[v][key]
            stats["paid_group_entries"] += 1
        tables.append(Table(frozenset((v,)), incident, data))
    return tables


def merge_tables(left, right, dimensions, ring, stats):
    """Exact matrix-shaped contraction; classical backend for verification."""
    if left.vertices & right.vertices:
        raise ValueError("cannot merge overlapping group sets")
    shared = tuple(sorted(set(left.edges) & set(right.edges)))
    boundary = tuple(sorted(set(left.edges) ^ set(right.edges)))
    data = {}
    for outside in assignments(boundary, dimensions):
        value = ring.zero
        for inside in assignments(shared, dimensions):
            assignment = outside | inside
            lk = tuple(assignment[e] for e in left.edges)
            rk = tuple(assignment[e] for e in right.edges)
            value = ring.add(value, ring.mul(left.data[lk], right.data[rk]))
            stats["scalar_products"] += 1
        data[tuple(outside[e] for e in boundary)] = value
    stats["largest_table_cells"] = max(stats["largest_table_cells"], len(data))
    stats["merges"] += 1
    return Table(left.vertices | right.vertices, boundary, data)


def contract_nine(dimensions, factor_entries, ring):
    """Select 3+3+3 adaptively; build pair/triple tables; contract the triangle."""
    chosen = select_partition(dimensions)
    partition = chosen[0]
    stats = {"paid_group_entries": 0, "scalar_products": 0,
             "largest_table_cells": 0, "merges": 0}
    singles = singleton_tables(dimensions, factor_entries, stats)
    stats["largest_table_cells"] = max(len(t.data) for t in singles)
    triples = []
    for a, b, c in partition:
        pair = merge_tables(singles[a], singles[b], dimensions, ring, stats)
        triples.append(merge_tables(pair, singles[c], dimensions, ring, stats))
    combined = merge_tables(triples[0], triples[1], dimensions, ring, stats)
    final = merge_tables(combined, triples[2], dimensions, ring, stats)
    if final.edges or final.vertices != frozenset(VERTICES):
        raise RuntimeError("contraction did not eliminate every index")
    return final.data[()], {"partition": partition,
                           "triangle_dimensions": chosen[3], **stats}


def direct_contraction(dimensions, factor_entries, ring):
    """Independent definition: enumerate every edge index, then all factors."""
    active = tuple(sorted(e for e, d in dimensions.items() if d > 1))
    incident = {v: tuple(e for e in active if v in e) for v in VERTICES}
    answer = ring.zero
    for assignment in assignments(active, dimensions):
        term = ring.one
        for v in VERTICES:
            key = tuple(assignment[e] for e in incident[v])
            term = ring.mul(term, factor_entries[v][key])
        answer = ring.add(answer, term)
    return answer
