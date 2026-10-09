"""Disk-completion quotient over F_2; actual separated boundary intervals.

No routine in this module certifies an embedding in a knot exterior.
A Morphism is a disk union, with inputs before outputs. None denotes a
composition containing a cycle or a component with no external interval.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Iterable, Optional

Partition = tuple[int, ...]


def canonical(labels: Iterable[int]) -> Partition:
    renaming: dict[int, int] = {}
    return tuple(renaming.setdefault(x, len(renaming)) for x in labels)


def validate_partition(p: Partition) -> None:
    if not p or any(type(x) is not int or x < 0 for x in p) or canonical(p) != p:
        raise ValueError("A partition must be nonempty, canonical, and nonnegative")


def blocks(p: Partition) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(i for i, x in enumerate(p) if x == a)
                 for a in range(max(p) + 1))


def partitions(n: int) -> Iterable[Partition]:
    if n < 1:
        raise ValueError("n must be positive")
    def rec(p: Partition):
        if len(p) == n:
            yield p
        else:
            for a in range(max(p) + 2):
                yield from rec(p + (a,))
    return rec((0,))


def feature(p: Partition) -> int:
    """Packed 2^(r-1)-bit vector: omitted rows are a block transversal."""
    validate_partition(p)
    return _feature_cached(p)


@lru_cache(maxsize=32768)
def _feature_cached(p: Partition) -> int:
    bs = blocks(p)
    root = bs[0]  # canonical label zero contains interval zero
    masks = [sum(1 << (i - 1) for i in root if i)]
    for block in bs[1:]:
        masks = [mask | sum(1 << (i - 1) for i in block if i != omit)
                 for mask in masks for omit in block]
    out = 0
    for mask in masks:
        out ^= 1 << mask
    return out


def binary_rank(rows: Iterable[int]) -> int:
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            lead = row.bit_length() - 1
            if lead in pivots:
                row ^= pivots[lead]
            else:
                pivots[lead] = row
                break
    return len(pivots)


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def root(self, a: int) -> int:
        while a != self.parent[a]:
            self.parent[a] = self.parent[self.parent[a]]
            a = self.parent[a]
        return a

    def join(self, a: int, b: int) -> bool:
        a, b = self.root(a), self.root(b)
        if a == b:
            return False
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]
        return True


@dataclass(frozen=True)
class Morphism:
    source: int
    target: int
    partition: Partition

    def __post_init__(self):
        if type(self.source) is not int or type(self.target) is not int:
            raise ValueError("Object sizes must be integers")
        if self.source < 1 or self.target < 1:
            raise ValueError("This category has positive objects only")
        validate_partition(self.partition)
        if len(self.partition) != self.source + self.target:
            raise ValueError("Partition length disagrees with the object sizes")


def identity(b: int) -> Morphism:
    return Morphism(b, b, tuple(range(b)) * 2)


def compose(first: Optional[Morphism], second: Optional[Morphism]) -> Optional[Morphism]:
    """Return second o first. Reject cyclic and sealed components."""
    if first is None or second is None:
        return None
    if first.target != second.source:
        raise ValueError("Mismatched composition interface")
    a, b, c = first.source, first.target, second.target
    p, q = first.partition, second.partition
    np, nq = max(p) + 1, max(q) + 1
    dsu = DSU(np + nq)
    for i in range(b):
        if not dsu.join(p[a + i], np + q[i]):
            return None
    outer = [dsu.root(x) for x in p[:a]] + [dsu.root(np + x) for x in q[b:]]
    if set(outer) != {dsu.root(i) for i in range(np + nq)}:
        return None
    return Morphism(a, c, canonical(outer))


def tensor(p: Optional[Morphism], q: Optional[Morphism]) -> Optional[Morphism]:
    if p is None or q is None:
        return None
    offset = max(p.partition) + 1
    a, b = p.source, q.source
    labels = (p.partition[:a] + tuple(offset + x for x in q.partition[:b])
              + p.partition[a:] + tuple(offset + x for x in q.partition[b:]))
    return Morphism(a + b, p.target + q.target, canonical(labels))


def flip(p: Morphism) -> Morphism:
    return Morphism(p.target, p.source,
                    canonical(p.partition[p.source:] + p.partition[:p.source]))


def disk_cap(p: Partition, q: Partition) -> bool:
    """The direct component-incidence tree predicate, not a parity count."""
    validate_partition(p)
    validate_partition(q)
    if len(p) != len(q):
        raise ValueError("Cap has the wrong number of intervals")
    np, nq = max(p) + 1, max(q) + 1
    if np + nq != len(p) + 1:
        return False
    dsu = DSU(np + nq)
    return all(dsu.join(x, np + y) for x, y in zip(p, q))


def cap_pairing(p: Partition, q: Partition) -> int:
    if len(p) != len(q):
        raise ValueError("Cap size mismatch")
    v, w = feature(p), feature(q)
    top = (1 << (len(p) - 1)) - 1
    parity = 0
    while v:
        bit = v & -v
        mask = bit.bit_length() - 1
        parity ^= (w >> (top ^ mask)) & 1
        v ^= bit
    return parity


@lru_cache(maxsize=32)
def splitters(b: int) -> tuple[tuple[Morphism, ...], tuple[Morphism, ...]]:
    """U_i:1->b, V_i:b->1, V_i U_j=delta_ij, sum U_i V_i=I_b."""
    if b < 1:
        raise ValueError("Object size must be positive")
    if b == 1:
        return ((identity(1),), (identity(1),))
    u = (Morphism(1, 2, (0, 0, 0)), Morphism(1, 2, (0, 0, 1)))
    v = (Morphism(2, 1, (0, 1, 0)), Morphism(2, 1, (0, 0, 0)))
    if b == 2:
        return u, v
    prev_u, prev_v = splitters(b - 1)
    ident = identity(b - 2)
    us, vs = [], []
    for i in range(len(prev_u)):
        for j in range(2):
            up = compose(prev_u[i], tensor(ident, u[j]))
            down = compose(tensor(ident, v[j]), prev_v[i])
            assert up is not None and down is not None
            us.append(up)
            vs.append(down)
    return tuple(us), tuple(vs)


def dual_scalar(p: Optional[Morphism]) -> int:
    """Encode a+b epsilon as a+2b; epsilon^2=0."""
    if p is None:
        return 0
    if p.source != 1 or p.target != 1:
        raise ValueError("Not an endomorphism of object 1")
    return 1 if p.partition == (0, 0) else 2


def dual_multiply(x: int, y: int) -> int:
    return ((x & 1) & (y & 1)) | (((((x >> 1) & (y & 1)) ^ ((y >> 1) & (x & 1))) & 1) << 1)


@lru_cache(maxsize=4096)
def matrix(p: Morphism) -> tuple[tuple[int, ...], ...]:
    us, _ = splitters(p.source)
    _, vs = splitters(p.target)
    return tuple(tuple(dual_scalar(compose(compose(u, p), v)) for u in us) for v in vs)


def matrix_product(a, b):
    """Ordinary product a*b over the dual numbers (not tropical)."""
    if not a or not b or len(a[0]) != len(b):
        raise ValueError("Matrix dimensions disagree")
    out = []
    for row in a:
        vals = []
        for j in range(len(b[0])):
            x = 0
            for k in range(len(b)):
                x ^= dual_multiply(row[k], b[k][j])
            vals.append(x)
        out.append(tuple(vals))
    return tuple(out)


def matrix_trace_epsilon(a) -> int:
    if len(a) != len(a[0]):
        raise ValueError("Trace requires a square matrix")
    out = 0
    for i in range(len(a)):
        out ^= (a[i][i] >> 1) & 1
    return out
