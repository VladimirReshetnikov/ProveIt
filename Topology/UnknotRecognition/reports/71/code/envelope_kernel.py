"""Certified minimum-cost disk representatives in a two-sided envelope.

A label denotes one genuine, disjoint boundary arc, not a bundle of arcs.
These routines solve a finite-interface problem; they do not recognize knots.
Python 3.10+, standard library only. See article.tex for precise contracts.
"""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from math import comb
from time import monotonic
from typing import Callable, Iterable, Sequence
import json

Partition = tuple[int, ...]
Tick = Callable[[], None] | None


class ResourceLimit(RuntimeError):
    """An incomplete computation; never evidence of infeasibility."""


class Budget:
    def __init__(self, seconds: float | None = None, steps: int | None = None):
        if seconds is not None and seconds < 0:
            raise ValueError("seconds must be nonnegative")
        if steps is not None and (type(steps) is not int or steps < 0):
            raise ValueError("steps must be a nonnegative integer")
        self.deadline = None if seconds is None else monotonic() + seconds
        self.remaining = steps

    def __call__(self) -> None:
        if self.remaining is not None:
            if self.remaining == 0:
                raise ResourceLimit("operation budget exhausted")
            self.remaining -= 1
        if self.deadline is not None and monotonic() >= self.deadline:
            raise ResourceLimit("time budget exhausted")


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, x: int, y: int) -> bool:
        x, y = self.find(x), self.find(y)
        if x == y:
            return False
        if self.size[x] < self.size[y]:
            x, y = y, x
        self.parent[y] = x
        self.size[x] += self.size[y]
        return True


def canonical(values: Iterable[int]) -> Partition:
    labels: dict[int, int] = {}
    out: list[int] = []
    for value in values:
        if type(value) is not int or value < 0:
            raise ValueError("partition labels must be nonnegative integers")
        if value not in labels:
            labels[value] = len(labels)
        out.append(labels[value])
    return tuple(out)


def validate(p: Sequence[int], *, nonempty: bool = True) -> Partition:
    p = tuple(p)
    if nonempty and not p:
        raise ValueError("an intermediate interface must be nonempty")
    if canonical(p) != p:
        raise ValueError("partition must be in restricted-growth canonical form")
    return p


def blocks(p: Sequence[int]) -> tuple[tuple[int, ...], ...]:
    groups: dict[int, list[int]] = {}
    for i, x in enumerate(p):
        groups.setdefault(x, []).append(i)
    return tuple(tuple(group) for group in groups.values())


def count(p: Sequence[int]) -> int:
    return len(set(p))


def refines(p: Sequence[int], envelope: Sequence[int]) -> bool:
    if len(p) != len(envelope):
        return False
    owner: dict[int, int] = {}
    for small, large in zip(p, envelope):
        if small in owner and owner[small] != large:
            return False
        owner[small] = large
    return True


def join(partitions: Sequence[Sequence[int]], n: int | None = None) -> Partition:
    if n is None:
        if not partitions:
            raise ValueError("specify n for the join of an empty family")
        n = len(partitions[0])
    dsu = DSU(n)
    for p in partitions:
        if len(p) != n:
            raise ValueError("inconsistent partition widths")
        for block in blocks(p):
            for x in block[1:]:
                dsu.union(block[0], x)
    return canonical(dsu.find(i) for i in range(n))


def disk_compatible(p: Sequence[int], q: Sequence[int]) -> bool:
    """Direct tree predicate, independent of the exterior representation."""
    if len(p) != len(q) or not p:
        return False
    if count(p) + count(q) != len(p) + 1:
        return False
    return count(join([p, q])) == 1


def partitions(n: int) -> Iterable[Partition]:
    """All partitions, for small exhaustive audits only; never used by the solver."""
    if n < 0:
        raise ValueError("negative width")
    if n == 0:
        yield ()
        return
    def rec(prefix: tuple[int, ...], highest: int):
        if len(prefix) == n:
            yield prefix
        else:
            for x in range(highest + 2):
                yield from rec(prefix + (x,), max(highest, x))
    yield from rec((0,), 0)


def pack_support(support: Iterable[int], dimension: int) -> int:
    data = bytearray((dimension + 7) // 8)
    for mask in support:
        data[mask >> 3] |= 1 << (mask & 7)
    return int.from_bytes(data, "little")


def exterior_row(rows: Sequence[int], lam: int, tick: Tick = None) -> int:
    """All maximal minors over F_2, coordinate indexed by subset bit mask.

    Sparse exterior multiplication; the empty wedge is the scalar 1.
    """
    if len(rows) > lam:
        return 0
    support = {0}
    full = (1 << lam) - 1
    for row in rows:
        if tick:
            tick()
        if row < 0 or row & ~full:
            raise ValueError("constraint outside cycle coordinates")
        nxt: set[int] = set()
        for mask in support:
            if tick:
                tick()
            available = row & ~mask
            while available:
                bit = available & -available
                available -= bit
                target = mask | bit
                if target in nxt:
                    nxt.remove(target)
                else:
                    nxt.add(target)
        support = nxt
        if not support:
            return 0
    return pack_support(support, 1 << lam)


def complementary_pairing(v: int, w: int, lam: int) -> int:
    full = (1 << lam) - 1
    answer = 0
    while v:
        bit = v & -v
        v -= bit
        mask = bit.bit_length() - 1
        answer ^= (w >> (full ^ mask)) & 1
    return answer


@dataclass(frozen=True)
class Candidate:
    partition: Partition
    cost: int = 0
    sector: int = 0
    witness: tuple[int, ...] = ()

    def __post_init__(self):
        object.__setattr__(self, "partition", validate(self.partition))
        if type(self.cost) is not int:
            raise ValueError("cost must be an exact integer")
        if type(self.sector) is not int or not 0 <= self.sector < 4:
            raise ValueError("sector must be a two-bit label")
        if not isinstance(self.witness, tuple) or any(type(x) is not int or x < 0 for x in self.witness):
            raise ValueError("witness must be a tuple of nonnegative choice indices")


class Envelope:
    """Coarse past/future partitions and their bipartite incidence cycle space."""
    def __init__(self, sigma: Sequence[int], rho: Sequence[int],
                 max_cycle_rank: int | None = 18, tick: Tick = None):
        self.sigma, self.rho = validate(sigma), validate(rho)
        if len(sigma) != len(rho):
            raise ValueError("envelope widths disagree")
        self.r = len(sigma)
        self.s, self.t = count(sigma), count(rho)
        self.edges = tuple((self.sigma[e], self.s + self.rho[e]) for e in range(self.r))
        dsu = DSU(self.s + self.t)
        tree, chords = [], []
        adj: list[list[tuple[int, int]]] = [[] for _ in range(self.s + self.t)]
        for e, (u, v) in enumerate(self.edges):
            if tick:
                tick()
            if dsu.union(u, v):
                tree.append(e)
                adj[u].append((v, e)); adj[v].append((u, e))
            else:
                chords.append(e)
        self.components = len({dsu.find(v) for v in range(self.s + self.t)})
        self.connected = self.components == 1
        self.lam = len(chords) if self.connected else None
        self.tree, self.chords = tuple(tree), tuple(chords)
        self.cycles: tuple[int, ...] = ()
        self.edge_coordinates: tuple[int, ...] = ()
        if not self.connected:
            return
        assert self.lam == self.r + 1 - self.s - self.t
        if max_cycle_rank is not None and self.lam > max_cycle_rank:
            raise ResourceLimit(f"cycle rank {self.lam} exceeds allocation guard {max_cycle_rank}")
        cycles: list[int] = []
        coords = [0] * self.r
        for index, e in enumerate(chords):
            if tick:
                tick()
            u, v = self.edges[e]
            parent: dict[int, tuple[int, int]] = {u: (-1, -1)}
            stack = [u]
            while stack and v not in parent:
                x = stack.pop()
                for y, f in adj[x]:
                    if y not in parent:
                        parent[y] = (x, f)
                        stack.append(y)
            cycle = 1 << e
            x = v
            while x != u:
                x, f = parent[x]
                cycle |= 1 << f
            cycles.append(cycle)
            z = cycle
            while z:
                bit = z & -z; z -= bit
                coords[bit.bit_length() - 1] |= 1 << index
        self.cycles = tuple(cycles)
        self.edge_coordinates = tuple(coords)

    def constraints(self, p: Sequence[int], side: str = "past") -> tuple[int, ...]:
        coarse = self.sigma if side == "past" else self.rho if side == "future" else None
        if coarse is None:
            raise ValueError("side must be past or future")
        validate(p)
        if not refines(p, coarse):
            raise ValueError("candidate does not refine its certified envelope")
        if not self.connected:
            return ()
        # Omit the first subblock inside every original coarse vertex.
        # Its parity follows from the others because each cycle has even incidence.
        seen: set[int] = set()
        rows: list[int] = []
        for block in blocks(p):
            parent = coarse[block[0]]
            if parent not in seen:
                seen.add(parent)
                continue
            row = 0
            for e in block:
                row ^= self.edge_coordinates[e]
            rows.append(row)
        return tuple(rows)

    def viable(self, p: Sequence[int], side: str = "past") -> bool:
        if side not in ("past", "future"):
            raise ValueError("side must be past or future")
        validate(p)
        coarse = self.sigma if side == "past" else self.rho
        other = self.rho if side == "past" else self.sigma
        if not refines(p, coarse):
            raise ValueError("candidate outside envelope")
        return self.connected and count(join([p, other])) == 1

    def feature(self, p: Sequence[int], side: str = "past", tick: Tick = None) -> int:
        rows = self.constraints(p, side)
        if not self.connected:
            return 0
        return exterior_row(rows, self.lam, tick)

    def coordinate_partition(self, subset: int, side: str = "past") -> Partition:
        """Chord-detachment witness giving one unit exterior coordinate."""
        if side not in ("past", "future"):
            raise ValueError("side must be past or future")
        if type(subset) is not int or not self.connected or subset < 0 or subset >= (1 << self.lam):
            raise ValueError("invalid coordinate subset")
        coarse = self.sigma if side == "past" else self.rho
        labels = list(coarse)
        fresh = count(coarse)
        for i, e in enumerate(self.chords):
            if subset >> i & 1:
                labels[e] = fresh
                fresh += 1
        return canonical(labels)


def root_feature(p: Sequence[int], max_width: int | None = 20, tick: Tick = None) -> int:
    """Unrestricted predecessor factor, included only as a fair comparator."""
    r = len(p)
    if max_width is not None and r > max_width:
        raise ResourceLimit("root-feature width allocation guard")
    bs = blocks(p)
    support = {0}
    for block in bs:
        if 0 in block:
            continue
        nxt = set()
        for mask in support:
            if tick:
                tick()
            for e in block:
                nxt.add(mask | (1 << (e - 1)))
        support = nxt
    return pack_support(support, 1 << (r - 1))


def source_digest(items: Sequence[Candidate], sigma: Sequence[int], rho: Sequence[int]) -> str:
    source = {"sigma": list(sigma), "rho": list(rho),
              "items": [{"partition": list(c.partition), "cost_hex": hex(c.cost),
                         "sector": c.sector, "witness": list(c.witness)} for c in items]}
    return sha256(json.dumps(source, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


@dataclass
class Reduction:
    retained: tuple[int, ...]
    certificate: dict
    row_count: int
    nonzero_count: int
    lam: int | None


def reduce_family(items: Sequence[Candidate], envelope: Envelope, *,
                  mode: str = "cycle", tick: Tick = None,
                  max_root_width: int | None = 20) -> Reduction:
    """Keep actual original candidates; certify every discarded vector.

    Sectors are reduced separately. The source must independently certify that
    all legal past/future partitions refine sigma/rho. An envelope digest alone
    cannot certify that geometric assertion.
    """
    if mode not in {"cycle", "root"}:
        raise ValueError("unknown reduction mode")
    for c in items:
        if len(c.partition) != envelope.r or not refines(c.partition, envelope.sigma):
            raise ValueError("candidate outside past envelope")
    order = sorted(range(len(items)), key=lambda i: (items[i].cost, i))
    # Pivot entries: residual vector, XOR of original retained positions.
    pivots: dict[tuple[int, int], tuple[int, int]] = {}
    retained: list[int] = []
    expansion_masks = [0] * len(items)
    cache: dict[Partition, int] = {}
    nonzero = 0
    for i in order:
        if tick:
            tick()
        c = items[i]
        if c.partition not in cache:
            if mode == "cycle":
                cache[c.partition] = envelope.feature(c.partition, tick=tick)
            else:
                # Give the stronger-root baseline the SAME cheap feasibility pruning.
                cache[c.partition] = (root_feature(c.partition, max_root_width, tick)
                                      if envelope.viable(c.partition) else 0)
        value = cache[c.partition]
        nonzero += value != 0
        expression = 0
        while value:
            if tick:
                tick()
            pivot = value.bit_length() - 1
            key = (c.sector, pivot)
            if key not in pivots:
                position = len(retained)
                retained.append(i)
                pivots[key] = (value, expression ^ (1 << position))
                expansion_masks[i] = 1 << position
                break
            vector, combination = pivots[key]
            value ^= vector
            expression ^= combination
        else:
            expansion_masks[i] = expression
    expansions = []
    for mask in expansion_masks:
        row = []
        while mask:
            bit = mask & -mask; mask -= bit
            row.append(retained[bit.bit_length() - 1])
        expansions.append(row)
    certificate = {"schema": "cycle-envelope-reduction-v1", "mode": mode,
                   "source_sha256": source_digest(items, envelope.sigma, envelope.rho),
                   "retained": retained, "expansions": expansions}
    return Reduction(tuple(retained), certificate, len(items), nonzero, envelope.lam)
