"""Validated, source-neutral input. Counts are UNSIGNED, never reduced modulo p."""
from __future__ import annotations
from dataclasses import dataclass
import hashlib
import json
from typing import Iterable


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, a: int) -> int:
        while self.parent[a] != a:
            self.parent[a] = self.parent[self.parent[a]]
            a = self.parent[a]
        return a

    def union(self, a: int, b: int) -> bool:
        a, b = self.find(a), self.find(b)
        if a == b:
            return False
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]
        return True


def _count(x: object) -> int:
    if type(x) is str and x.startswith('0x'):
        x = int(x, 16)
    if type(x) is not int or x < 0:
        raise ValueError('coefficients must be nonnegative integers or hexadecimal strings')
    return x


@dataclass(frozen=True)
class Instance:
    vertices: int
    edges: tuple[tuple[int, int], ...]
    matrix: tuple[tuple[int, ...], ...]
    columns: int

    def __post_init__(self) -> None:
        if type(self.vertices) is not int or self.vertices < 1:
            raise ValueError('vertices must be positive')
        if type(self.columns) is not int or self.columns < 0:
            raise ValueError('columns must be nonnegative')
        if len(self.edges) != len(self.matrix):
            raise ValueError('one dual edge is required for every matrix row')
        if self.vertices > len(self.edges) + 1:
            raise ValueError('too many vertices for the explicitly listed connected graph')
        d = DSU(self.vertices)
        for u, v in self.edges:
            if any(type(w) is not int or not 0 <= w < self.vertices for w in (u, v)):
                raise ValueError('dual endpoint out of range')
            d.union(u, v)
        if any(d.find(v) != d.find(0) for v in range(self.vertices)):
            raise ValueError('dual graph must be connected, including its boundary root 0')
        for row in self.matrix:
            if len(row) != self.columns or any(type(x) is not int or x < 0 for x in row):
                raise ValueError('malformed unsigned matrix')

    @property
    def m(self) -> int:
        return len(self.edges)

    @classmethod
    def from_dict(cls, data: dict) -> 'Instance':
        if type(data) is not dict:
            raise ValueError('input must be a JSON object')
        rows = tuple(tuple(_count(x) for x in row) for row in data['matrix'])
        return cls(data['vertices'], tuple(tuple(e) for e in data['edges']), rows,
                   data.get('columns', len(rows[0]) if rows else 0))

    def to_dict(self) -> dict:
        return dict(schema='activation-forest-instance-v1', vertices=self.vertices,
                    columns=self.columns, edges=[list(e) for e in self.edges],
                    matrix=[[x if x.bit_length() < 1024 else hex(x) for x in row]
                            for row in self.matrix])

    def digest(self) -> str:
        # Hexadecimal normalization handles very large binary counts without
        # Python's decimal-string conversion limit. The digest is NOT a geometry proof.
        data = [self.vertices, self.columns, self.edges,
                [[hex(x) for x in row] for row in self.matrix]]
        return hashlib.sha256(json.dumps(data, separators=(',', ':')).encode()).hexdigest()


def forest(inst: Instance, selected: Iterable[int]) -> bool:
    d = DSU(inst.vertices)
    used = set()
    for e in selected:
        if type(e) is not int or not 0 <= e < inst.m or e in used:
            return False
        used.add(e)
        if not d.union(*inst.edges[e]):
            return False
    return True


def extend_tree(inst: Instance, selected: Iterable[int]) -> list[int]:
    out = list(selected)
    if not forest(inst, out):
        raise ValueError('cannot extend a dependent edge set')
    d = DSU(inst.vertices)
    for e in out:
        d.union(*inst.edges[e])
    for e, pair in enumerate(inst.edges):
        if d.union(*pair):
            out.append(e)
    if len(out) != inst.vertices - 1:
        raise AssertionError('validated connected graph failed tree extension')
    return sorted(out)


def peel(inst: Instance, deleted: Iterable[int]) -> list[list[int]] | None:
    """Simple deterministic dense producer; independent checker is in verify.py."""
    live = set(range(inst.m)) - set(deleted)
    if not live:
        return []
    cols = set(range(inst.columns))
    pivots = []
    while live:
        pivot = None
        for h in sorted(cols):
            support = [e for e in sorted(live) if inst.matrix[e][h]]
            if len(support) == 1 and inst.matrix[support[0]][h] == 1:
                pivot = (support[0], h)
                break
        if pivot is None:
            return None
        e, h = pivot
        pivots.append([e, h])
        live.remove(e)
        cols.remove(h)
    return pivots
