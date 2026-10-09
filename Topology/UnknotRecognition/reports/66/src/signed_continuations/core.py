"""Exact signed-partition continuation bases. Standard library, Python >=3.10.

This module answers finite interface optimization queries, not unknot recognition.
A geometry key is an opaque, caller-certified compatibility class. Resource
failures are exceptions; no resource failure is converted to a topology verdict.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import defaultdict
from typing import Iterable, Sequence

class BudgetExceeded(RuntimeError):
    """The requested exact operation exceeds its declared resource budget."""

def integer(value: object, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer (not bool)")
    return value

@dataclass(frozen=True, slots=True)
class SignedPartition:
    labels: tuple[int, ...]
    offsets: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.labels) is not tuple or type(self.offsets) is not tuple:
            raise TypeError("labels and offsets must be tuples")
        if not self.labels or len(self.labels) != len(self.offsets):
            raise ValueError("a nonempty interface and equal lengths are required")
        seen = set()
        for a, b in zip(self.labels, self.offsets):
            integer(a, "label"); integer(b, "offset")
            if b not in (0, 1):
                raise ValueError("offset must be zero or one")
            if a not in seen:
                if a != len(seen) or b != 0:
                    raise ValueError("not a canonical signed partition")
                seen.add(a)

    @property
    def r(self) -> int:
        return len(self.labels)

    @property
    def blocks(self) -> int:
        return max(self.labels) + 1

    @classmethod
    def canonical(cls, labels: Sequence[int], offsets: Sequence[int]) -> SignedPartition:
        if not labels or len(labels) != len(offsets):
            raise ValueError("nonempty equal-length arrays required")
        anchors: dict[int, tuple[int, int]] = {}
        out_l, out_p = [], []
        for a, b in zip(labels, offsets):
            integer(a, "label"); integer(b, "offset")
            if b not in (0, 1):
                raise ValueError("nonbinary offset")
            if a not in anchors:
                anchors[a] = (len(anchors), b)
            k, gauge = anchors[a]
            out_l.append(k); out_p.append(b ^ gauge)
        return cls(tuple(out_l), tuple(out_p))

    @classmethod
    def discrete(cls, r: int) -> SignedPartition:
        integer(r, "r")
        if r < 1:
            raise ValueError("r must be positive")
        return cls(tuple(range(r)), (0,) * r)

    @classmethod
    def from_edges(cls, r: int, edges: Iterable[tuple[int, int, int]]) -> SignedPartition | None:
        """Parity DSU; None means a contradictory parity cycle."""
        integer(r, "r")
        if r < 1:
            raise ValueError("r must be positive")
        parent, size, parity = list(range(r)), [1] * r, [0] * r
        def find(a: int) -> tuple[int, int]:
            p = 0
            while parent[a] != a:
                p ^= parity[a]; a = parent[a]
            return a, p
        for edge in edges:
            if len(edge) != 3:
                raise ValueError("edges must have three entries")
            a, b, p = edge
            integer(a, "endpoint"); integer(b, "endpoint"); integer(p, "parity")
            if not (0 <= a < r and 0 <= b < r and p in (0, 1)):
                raise ValueError("invalid signed edge")
            ra, pa = find(a); rb, pb = find(b)
            if ra == rb:
                if pa ^ pb != p:
                    return None
            else:
                if size[ra] < size[rb]:
                    ra, rb = rb, ra
                parent[rb] = ra
                parity[rb] = pa ^ pb ^ p
                size[ra] += size[rb]
        pairs = [find(i) for i in range(r)]
        return cls.canonical([a for a, _ in pairs], [b for _, b in pairs])

    def edges(self) -> tuple[tuple[int, int, int], ...]:
        roots: dict[int, int] = {}
        out = []
        for i, (k, p) in enumerate(zip(self.labels, self.offsets)):
            if k in roots:
                out.append((roots[k], i, p))
            else:
                roots[k] = i
        return tuple(out)

    def join(self, other: SignedPartition) -> SignedPartition | None:
        if self.r != other.r:
            raise ValueError("interface widths differ")
        return self.from_edges(self.r, self.edges() + other.edges())

    def add_edge(self, a: int, b: int, p: int) -> SignedPartition | None:
        return self.from_edges(self.r, self.edges() + ((a, b, p),))

    def introduce(self) -> SignedPartition:
        return SignedPartition(self.labels + (self.blocks,), self.offsets + (0,))

    def restrict(self, keep: Sequence[int], *, reject_orphans: bool = True) -> SignedPartition | None:
        """Reorder/restrict ports. Reject a component losing all live ports."""
        if not keep:
            raise ValueError("use an explicit terminal query before removing the last port")
        if any(type(i) is not int or i < 0 or i >= self.r for i in keep) or len(set(keep)) != len(keep):
            raise ValueError("keep must contain distinct valid indices")
        if reject_orphans and {self.labels[i] for i in keep} != set(self.labels):
            return None
        return self.canonical([self.labels[i] for i in keep], [self.offsets[i] for i in keep])

    def gauge(self, flips: Sequence[int]) -> SignedPartition:
        if len(flips) != self.r or any(type(x) is not int or x not in (0, 1) for x in flips):
            raise ValueError("one binary flip per port required")
        return self.canonical(self.labels, [a ^ b for a, b in zip(self.offsets, flips)])

    def disjoint(self, other: SignedPartition) -> SignedPartition:
        return SignedPartition(self.labels + tuple(k + self.blocks for k in other.labels),
                               self.offsets + other.offsets)

    def vector(self, *, max_dimension: int = 1 << 20) -> int:
        """Anchored satisfying assignments, as a packed binary row.

        Port zero has spin zero. Assignment index j stores the spins of ports
        1,...,r-1 in increasing bit order. Gray enumeration visits only support.
        """
        integer(max_dimension, "max_dimension")
        if max_dimension < 1 or self.r - 1 >= max_dimension.bit_length():
            raise BudgetExceeded("cut-row dimension exceeds budget")
        d = 1 << (self.r - 1)
        if d > max_dimension:
            raise BudgetExceeded("cut-row dimension exceeds budget")
        base = sum(p << (i - 1) for i, p in enumerate(self.offsets) if i)
        masks = [0] * self.blocks
        for i, k in enumerate(self.labels):
            if i:
                masks[k] |= 1 << (i - 1)
        row = bytearray((d + 7) // 8)
        x = base
        row[x >> 3] |= 1 << (x & 7)
        for t in range(1, 1 << (self.blocks - 1)):
            j = (t & -t).bit_length()  # masks[1],...,masks[blocks-1]
            x ^= masks[j]
            row[x >> 3] |= 1 << (x & 7)
        return int.from_bytes(row, "little")

@dataclass(frozen=True, slots=True)
class Candidate:
    partition: SignedPartition
    cost: int
    token: str
    geometry_key: str = "abstract"
    def __post_init__(self) -> None:
        if not isinstance(self.partition, SignedPartition):
            raise TypeError("partition must be SignedPartition")
        integer(self.cost, "cost")
        if type(self.token) is not str or type(self.geometry_key) is not str:
            raise TypeError("token and geometry_key must be strings")

@dataclass(frozen=True, slots=True)
class BasisCertificate:
    selected: tuple[int, ...]
    expressions: tuple[int, ...]
    width: int
    geometry_key: str
    def as_dict(self) -> dict:
        return {"selected": list(self.selected), "expressions_hex": [hex(x) for x in self.expressions],
                "width": self.width, "geometry_key": self.geometry_key}

@dataclass(frozen=True, slots=True)
class Reduction:
    candidates: tuple[Candidate, ...]
    certificate: BasisCertificate
    rows: int
    xors: int
    dimension: int


def reduce_family(family: Sequence[Candidate], *, max_dimension: int = 1 << 20,
                  max_candidates: int = 1_000_000) -> Reduction:
    """Minimum-cost greedy binary basis, retaining original witnesses.

    Each input row is certified as an XOR of retained rows no more costly.
    Inputs must have one width and one geometry key. No geometry is inferred.
    """
    integer(max_candidates, "max_candidates")
    if len(family) > max_candidates or max_candidates < 0:
        raise BudgetExceeded("candidate budget exceeded")
    if not family:
        return Reduction((), BasisCertificate((), (), 0, ""), 0, 0, 0)
    r, key = family[0].partition.r, family[0].geometry_key
    if any(c.partition.r != r or c.geometry_key != key for c in family):
        raise ValueError("reduction across widths or geometry keys is forbidden")
    # Check dimension before sorting or allocating certificate arrays.
    family[0].partition.vector(max_dimension=max_dimension)
    selected: list[int] = []
    expressions = [0] * len(family)
    pivots: dict[int, tuple[int, int]] = {}
    xors = 0
    for i in sorted(range(len(family)), key=lambda i: (family[i].cost, i)):
        v = family[i].partition.vector(max_dimension=max_dimension)
        rep = 0
        while v:
            p = v.bit_length() - 1
            if p not in pivots:
                j = len(selected)
                selected.append(i)
                pivots[p] = (v, rep ^ (1 << j))
                expressions[i] = 1 << j
                break
            a, b = pivots[p]
            v ^= a; rep ^= b; xors += 1
        else:
            expressions[i] = rep
    cert = BasisCertificate(tuple(selected), tuple(expressions), r, key)
    return Reduction(tuple(family[i] for i in selected), cert, len(family), xors, 1 << (r - 1))


def compatible(a: SignedPartition, b: SignedPartition) -> bool:
    c = a.join(b)
    return c is not None and c.blocks == 1


def optimum(family: Sequence[Candidate], completion: SignedPartition) -> Candidate | None:
    """Exact minimum among connected, orientation-consistent completions."""
    best = None
    for c in family:
        if compatible(c.partition, completion) and (best is None or c.cost < best.cost):
            best = c
    return best


def partitions(r: int) -> Iterable[SignedPartition]:
    """All canonical binary-gain partitions; for bounded experiments only."""
    integer(r, "r")
    if r < 1:
        raise ValueError("positive width required")
    def rec(labels: tuple[int, ...], offsets: tuple[int, ...], blocks: int):
        if len(labels) == r:
            yield SignedPartition(labels, offsets)
            return
        for k in range(blocks):
            for p in (0, 1):
                yield from rec(labels + (k,), offsets + (p,), blocks)
        yield from rec(labels + (blocks,), offsets + (0,), blocks + 1)
    yield from rec((0,), (0,), 1)
