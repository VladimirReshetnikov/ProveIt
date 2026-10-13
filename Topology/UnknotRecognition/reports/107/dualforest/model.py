"""Validated, source-neutral inputs. Geometric source authentication is external."""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Mapping, Sequence


@dataclass(frozen=True)
class Instance:
    vertices: int
    edges: tuple[tuple[int, int], ...]
    rows: tuple[tuple[tuple[int, int], ...], ...]
    columns: int
    root: int = 0

    @property
    def m(self) -> int:
        return len(self.edges)

    def data(self) -> dict:
        return dict(schema="dual-forest-instance-v1", vertices=self.vertices,
                    root=self.root, columns=self.columns,
                    edges=[list(e) for e in self.edges],
                    rows=[[[c, w] for c, w in row] for row in self.rows])


class DSU:
    def __init__(self, n: int):
        self.p = list(range(n))
        self.rank = [0] * n
        self.components = n

    def find(self, x: int) -> int:
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a: int, b: int) -> bool:
        a, b = self.find(a), self.find(b)
        if a == b:
            return False
        if self.rank[a] < self.rank[b]:
            a, b = b, a
        self.p[b] = a
        if self.rank[a] == self.rank[b]:
            self.rank[a] += 1
        self.components -= 1
        return True


def make_instance(vertices: int, edges: Sequence[Sequence[int]],
                  rows: Sequence[Mapping[int, int]], *, columns: int | None = None,
                  root: int = 0) -> Instance:
    """Copy, validate, and saturate all positive incidences at two.

    Rows are indexed 0..m-1. Column labels are nonnegative integers.
    Loops and parallel dual edges are legal; the entire dual graph must connect.
    """
    if type(vertices) is not int or vertices < 1:
        raise ValueError("vertices must be a positive integer")
    if type(root) is not int or not 0 <= root < vertices:
        raise ValueError("invalid root")
    if len(edges) != len(rows):
        raise ValueError("one dual edge is required for every matrix row")
    # Connectivity forces v <= m+1. Check before allocating endpoint arrays;
    # a tiny untrusted JSON input must not request an enormous DSU.
    if vertices > len(edges) + 1:
        raise ValueError("too many vertices for a connected dual graph")
    ee = []
    ds = DSU(vertices)
    for edge in edges:
        if len(edge) != 2 or any(type(v) is not int or not 0 <= v < vertices for v in edge):
            raise ValueError("invalid dual edge")
        a, b = edge
        ee.append((a, b))
        ds.union(a, b)
    if ds.components != 1:
        raise ValueError("dual graph must be connected, including the root")
    rr = []
    maxcol = -1
    for row in rows:
        if not isinstance(row, Mapping):
            raise ValueError("each row must map column labels to incidences")
        out = []
        for c, w in row.items():
            if type(c) is not int or c < 0 or type(w) is not int or w < 0:
                raise ValueError("invalid nonnegative integer matrix entry")
            maxcol = max(maxcol, c)
            if w:
                out.append((c, min(w, 2)))
        rr.append(tuple(sorted(out)))
    if columns is None:
        columns = maxcol + 1
    if type(columns) is not int or columns < 0 or maxcol >= columns:
        raise ValueError("invalid column range")
    return Instance(vertices, tuple(ee), tuple(rr), columns, root)


def from_dense(vertices: int, edges: Sequence[Sequence[int]],
               matrix: Sequence[Sequence[int]], *, root: int = 0) -> Instance:
    n = len(matrix[0]) if matrix else 0
    if any(len(row) != n for row in matrix):
        raise ValueError("ragged matrix")
    return make_instance(vertices, edges, [dict(enumerate(row)) for row in matrix],
                         columns=n, root=root)


def from_data(data: dict) -> Instance:
    if not isinstance(data, dict) or data.get("schema") != "dual-forest-instance-v1":
        raise ValueError("unsupported instance schema")
    rows = []
    for row in data["rows"]:
        pairs = {}
        for c, w in row:
            if c in pairs:
                raise ValueError("duplicate column in a serialized row")
            pairs[c] = w
        rows.append(pairs)
    return make_instance(data["vertices"], data["edges"], rows,
                         columns=data["columns"], root=data["root"])


def rank(inst: Instance, edge_ids: Iterable[int]) -> int:
    d = DSU(inst.vertices)
    for r in edge_ids:
        d.union(*inst.edges[r])
    return inst.vertices - d.components


def extend_tree(inst: Instance, seed: Iterable[int]) -> list[int]:
    selected = sorted(set(seed))
    d = DSU(inst.vertices)
    for r in selected:
        if not d.union(*inst.edges[r]):
            raise ValueError("seed is not a graphic-independent set")
    picked = set(selected)
    for r, edge in enumerate(inst.edges):
        if r not in picked and d.union(*edge):
            selected.append(r)
    if d.components != 1:
        raise AssertionError("validated graph became disconnected")
    return sorted(selected)
