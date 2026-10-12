"""Corner-aware exact boundary gluing. SPDX-License-Identifier: MIT-0.

This module computes topology of abstract compact surfaces, not knot verdicts.
Boundary cycles on an orientable component must have coherent induced directions.
Large positive gap lengths are stored, never expanded by the kernel.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x: int) -> int:
        while x != self.parent[x]:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, x: int, y: int) -> None:
        x, y = self.find(x), self.find(y)
        if x == y:
            return
        if self.size[x] < self.size[y]:
            x, y = y, x
        self.parent[y] = x
        self.size[x] += self.size[y]


class ParityDSU:
    """Constraints value[x] XOR value[y] = bit, with inconsistency flags."""
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n
        self.parity = [0] * n
        self.bad = [False] * n

    def find(self, x: int) -> tuple[int, int]:
        y, bit = x, 0
        while self.parent[y] != y:
            bit ^= self.parity[y]
            y = self.parent[y]
        root, accum = y, 0
        while self.parent[x] != x:
            nxt, old = self.parent[x], self.parity[x]
            self.parent[x], self.parity[x] = root, bit ^ accum
            accum ^= old
            x = nxt
        return root, bit

    def union(self, x: int, y: int, bit: int) -> None:
        rx, px = self.find(x)
        ry, py = self.find(y)
        if rx == ry:
            if (px ^ py) != bit:
                self.bad[rx] = True
            return
        if self.size[rx] < self.size[ry]:
            rx, ry = ry, rx
        self.parent[ry] = rx
        self.parity[ry] = px ^ py ^ bit
        self.size[rx] += self.size[ry]
        self.bad[rx] |= self.bad[ry]


def natural(x: int, name: str) -> None:
    if type(x) is not int or x < 0:
        raise ValueError(f'{name} must be a nonnegative integer')


@dataclass(frozen=True)
class Surface:
    chi: int
    boundary: int
    orientable: bool = True

    def __post_init__(self):
        if type(self.chi) is not int or type(self.orientable) is not bool:
            raise ValueError('invalid surface data')
        natural(self.boundary, 'boundary')
        defect = 2 - self.boundary - self.chi
        if self.orientable:
            if defect < 0 or defect % 2:
                raise ValueError('invalid orientable surface characteristic')
        elif defect < 1:
            raise ValueError('invalid nonorientable surface characteristic')

    @property
    def genus_or_crosscaps(self) -> int:
        d = 2 - self.boundary - self.chi
        return d // 2 if self.orientable else d


@dataclass(frozen=True)
class Edge:
    """A labelled port (length one) or an unmarked positive gap.

    reverse=1 means that the port parameter opposes the cycle direction.
    Gap length is optional provenance; only its positivity affects topology.
    """
    port: str | None = None
    reverse: int = 0
    length: int = 1

    def __post_init__(self):
        if self.port is not None and (not isinstance(self.port, str) or not self.port):
            raise ValueError('a port label must be a nonempty string')
        if type(self.reverse) is not int or self.reverse not in (0, 1):
            raise ValueError('reverse must be 0 or 1')
        if type(self.length) is not int or self.length < 1:
            raise ValueError('gap lengths must be positive integers')
        if self.port is not None and self.length != 1:
            raise ValueError('ports are single marked cells')
        if self.port is None and self.reverse:
            raise ValueError('a gap has no port frame')


def normalize_word(edges: Iterable[Edge]) -> tuple[Edge, ...]:
    """Suppress all unmarked degree-two vertices; do not separate adjacent ports."""
    edges = list(edges)
    if any(not isinstance(e, Edge) for e in edges):
        raise ValueError('word elements must be Edge objects')
    if not edges or not any(e.port is not None for e in edges):
        return ()
    # Rotate to a port. This also combines a gap spanning the old cyclic origin.
    first = min((i for i, e in enumerate(edges) if e.port is not None),
                key=lambda i: edges[i].port)
    edges = edges[first:] + edges[:first]
    out: list[Edge] = []
    for e in edges:
        if not isinstance(e, Edge):
            raise ValueError('word elements must be Edge objects')
        if e.port is None and out and out[-1].port is None:
            out[-1] = Edge(length=out[-1].length + e.length)
        else:
            out.append(e)
    return tuple(out)


@dataclass(frozen=True)
class Cycle:
    surface: int
    edges: tuple[Edge, ...]


@dataclass(frozen=True)
class Kernel:
    surfaces: tuple[Surface, ...]
    cycles: tuple[Cycle, ...]

    def __post_init__(self):
        seen: set[str] = set()
        counts = [0] * len(self.surfaces)
        for s in self.surfaces:
            if not isinstance(s, Surface):
                raise ValueError('invalid surface object')
        for c in self.cycles:
            if not isinstance(c, Cycle):
                raise ValueError('invalid cycle object')
            natural(c.surface, 'surface index')
            if c.surface >= len(self.surfaces) or not c.edges:
                raise ValueError('invalid active cycle')
            if normalize_word(c.edges) != c.edges:
                raise ValueError('cycles must be normalized, with at least one port')
            counts[c.surface] += 1
            for e in c.edges:
                if e.port is not None:
                    if e.port in seen:
                        raise ValueError('duplicate port label')
                    seen.add(e.port)
        if any(c > s.boundary for c, s in zip(counts, self.surfaces)):
            raise ValueError('more active cycles than boundary components')

    @property
    def ports(self) -> tuple[str, ...]:
        return tuple(e.port for c in self.cycles for e in c.edges if e.port is not None)

    @property
    def passive(self) -> tuple[int, ...]:
        counts = [s.boundary for s in self.surfaces]
        for c in self.cycles:
            counts[c.surface] -= 1
        return tuple(counts)

    def to_dict(self) -> dict:
        # Hex strings avoid decimal digit limits on enormous binary integers.
        return {'schema': 'corner-surface-kernel-v1',
                'surfaces': [{'chi': hex(s.chi), 'boundary': hex(s.boundary),
                              'orientable': s.orientable} for s in self.surfaces],
                'cycles': [{'surface': c.surface,
                            'edges': [{'port': e.port, 'reverse': e.reverse,
                                       'length': hex(e.length)} for e in c.edges]}
                           for c in self.cycles]}

    @staticmethod
    def from_dict(data: dict) -> 'Kernel':
        if data.get('schema') != 'corner-surface-kernel-v1':
            raise ValueError('unsupported schema')
        return Kernel(tuple(Surface(int(s['chi'], 16), int(s['boundary'], 16),
                                    s['orientable']) for s in data['surfaces']),
                      tuple(Cycle(c['surface'], tuple(Edge(e['port'], e['reverse'],
                                   int(e['length'], 16)) for e in c['edges']))
                            for c in data['cycles']))


def make_kernel(surfaces: Iterable[Surface],
                cycles: Iterable[tuple[int, Iterable[Edge]]]) -> Kernel:
    out = []
    for owner, edges in cycles:
        word = normalize_word(edges)
        if word:
            out.append(Cycle(owner, word))
    return Kernel(tuple(surfaces), tuple(out))


@dataclass(frozen=True)
class Gluing:
    left: str
    right: str
    reverse: int = 1

    def __post_init__(self):
        if not isinstance(self.left, str) or not isinstance(self.right, str):
            raise ValueError('gluing labels must be strings')
        if self.left == self.right:
            raise ValueError('an edge cannot be paired with itself')
        if type(self.reverse) is not int or self.reverse not in (0, 1):
            raise ValueError('gluing reverse must be 0 or 1')


@dataclass(frozen=True)
class Result:
    kernel: Kernel
    sources: tuple[tuple[int, ...], ...]
    audit: dict


def glue(kernel: Kernel, gluings: Iterable[Gluing]) -> Result:
    """Apply disjoint pairings of entire marked boundary edges.

    The endpoint maps may preserve or reverse the supplied port parameters.
    Self-gluings of two DISTINCT edges on one surface and adjacent ports are
    supported. No 3-dimensional manifold conclusion is made.
    """
    gluings = tuple(gluings)
    n = len(kernel.surfaces)
    # edge rows: owner, start corner, end corner, Edge
    rows: list[tuple[int, int, int, Edge]] = []
    ports: dict[str, int] = {}
    vertex_owner: list[int] = []
    for c in kernel.cycles:
        offset, m = len(vertex_owner), len(c.edges)
        vertex_owner.extend([c.surface] * m)
        for j, edge in enumerate(c.edges):
            idx = len(rows)
            rows.append((c.surface, offset+j, offset+(j+1) % m, edge))
            if edge.port is not None:
                ports[edge.port] = idx
    used: set[str] = set()
    comp, corners, parity = DSU(n), DSU(len(vertex_owner)), ParityDSU(n)
    for i, s in enumerate(kernel.surfaces):
        parity.bad[i] = not s.orientable
    for g in gluings:
        if not isinstance(g, Gluing):
            raise ValueError('invalid gluing')
        if g.left not in ports or g.right not in ports:
            raise ValueError('unknown port')
        if g.left in used or g.right in used:
            raise ValueError('a port can be paired only once')
        used.update((g.left, g.right))
        i, u, v, a = rows[ports[g.left]]
        j, w, z, b = rows[ports[g.right]]
        flip = g.reverse ^ a.reverse ^ b.reverse
        corners.union(u, z if flip else w)
        corners.union(v, w if flip else z)
        comp.union(i, j)
        parity.union(i, j, 1 ^ flip)
    groups: dict[int, list[int]] = {}
    for i in range(n):
        groups.setdefault(comp.find(i), []).append(i)
    sources = tuple(sorted((tuple(v) for v in groups.values()), key=lambda v: v[0]))
    new_owner = {old: j for j, group in enumerate(sources) for old in group}
    q0, q1, pairs = [0]*len(sources), [set() for _ in sources], [0]*len(sources)
    for v, i in enumerate(vertex_owner):
        j = new_owner[i]
        q0[j] += 1
        q1[j].add(corners.find(v))
    for g in gluings:
        pairs[new_owner[rows[ports[g.left]][0]]] += 1
    orientable = []
    for group in sources:
        root, _ = parity.find(group[0])
        orientable.append(not parity.bad[root])
    # The unpaired boundary graph is 2-regular as a multigraph. Track endpoint
    # occurrences, not just sets of adjacent vertices (loops count twice).
    remain = [i for i, row in enumerate(rows) if row[3].port not in used]
    incident: dict[int, list[tuple[int, int]]] = {}
    for idx in remain:
        _, u, v, _ = rows[idx]
        incident.setdefault(corners.find(u), []).append((idx, 0))
        incident.setdefault(corners.find(v), []).append((idx, 1))
    if any(len(v) != 2 for v in incident.values()):
        raise ArithmeticError('boundary link failure')
    unseen = set(remain)
    active_cycles: list[Cycle] = []
    passive = kernel.passive
    boundary = [sum(passive[i] for i in group) for group in sources]
    for first in remain:
        if first not in unseen:
            continue
        owner = rows[first][0]
        group = new_owner[owner]
        # A coherent induced orientation is needed for composition on an
        # orientable output. Nonorientable output boundary directions are free.
        start_end = parity.find(owner)[1] if orientable[group] else 0
        current, enter = first, start_end
        word = []
        while True:
            if current not in unseen:
                raise ArithmeticError('boundary traversal repeated an edge')
            unseen.remove(current)
            old_owner, u, v, edge = rows[current]
            if orientable[group] and enter != parity.find(old_owner)[1]:
                raise ArithmeticError('input boundary orientations are incoherent')
            word.append(Edge(edge.port, edge.reverse ^ enter, 1)
                        if edge.port is not None else Edge(length=edge.length))
            exit_end = 1 ^ enter
            endpoint = corners.find((u, v)[exit_end])
            options = incident[endpoint]
            nxt = options[1] if options[0] == (current, exit_end) else options[0]
            if nxt == (first, start_end):
                break
            current, enter = nxt
        boundary[group] += 1
        word = normalize_word(word)
        if word:
            active_cycles.append(Cycle(group, word))
    new_surfaces = tuple(Surface(sum(kernel.surfaces[i].chi for i in group)
                                    + pairs[j] - (q0[j] - len(q1[j])),
                                boundary[j], orientable[j])
                         for j, group in enumerate(sources))
    return Result(Kernel(new_surfaces, tuple(active_cycles)), sources,
                  {'ports_before': len(ports), 'pairs': len(gluings),
                   'corners_before': q0, 'corners_after': [len(x) for x in q1],
                   'pairs_by_component': pairs,
                   'retained_edges_before': len(rows),
                   'retained_edges_after': sum(len(c.edges) for c in active_cycles)})


def signature(kernel: Kernel) -> tuple[tuple[int, int, bool], ...]:
    return tuple(sorted((s.chi, s.boundary, s.orientable) for s in kernel.surfaces))
