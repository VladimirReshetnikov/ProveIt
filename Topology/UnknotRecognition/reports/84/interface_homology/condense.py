"""Exact bounded-interface H_0/H_1 presentation assembly, standard library only."""
from __future__ import annotations
from dataclasses import dataclass, asdict
from .model import Model, validate, loop_chain, fingerprint


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def join(self, a: int, b: int) -> bool:
        a, b = self.find(a), self.find(b)
        if a == b:
            return False
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]
        return True


@dataclass(frozen=True)
class Condensation:
    schema: str
    source_sha256: str
    matrix: tuple[tuple[int, ...], ...]  # columns are relations
    relation_count: int  # preserves shape when there are zero rows
    core_generators: tuple[int, ...]  # non-tree edge numbers, zero based
    core_forest: tuple[int, ...]
    core_component: tuple[int, ...]  # component of each core vertex
    saturated_orientable: tuple[int, ...]
    saturated_nonorientable: tuple[int, ...]
    graph_vertices: int
    graph_edges: int
    graph_components: int
    graph_cycle_rank: int
    free_bulk: int
    two_torsion_bulk: int
    b0: int
    euler: int  # Euler characteristic of the abstract homotopy pushout
    surface_free: tuple[int, ...]  # per-copy local free ranks

    @property
    def rows(self) -> int:
        return len(self.matrix)

    def payload(self) -> dict:
        return asdict(self)


def condense(model: Model) -> Condensation:
    """No loop here has a bound equal to genus, crosscaps, or multiplicity.

    Returns the exact group coker(matrix) + Z^free_bulk + (Z/2)^two_torsion_bulk.
    Its interpretation as cut homology needs the separately verified geometric
    input contract in the article. It does not return a knot verdict.
    """
    validate(model)
    core = model.core
    forest = DSU(core.vertices)
    tree, generators = [], []
    for i, (u, v) in enumerate(core.edges):
        (tree if forest.join(u, v) else generators).append(i)
    roots = sorted({forest.find(v) for v in range(core.vertices)})
    root_index = {r: i for i, r in enumerate(roots)}
    component = tuple(root_index[forest.find(v)] for v in range(core.vertices))
    ported = [i for i, s in enumerate(model.surfaces) if s.attached]
    base_vertex = {i: len(roots) + j for j, i in enumerate(ported)}
    graph = DSU(len(roots) + len(ported))
    graph_edges = 0
    for i in ported:
        s = model.surfaces[i]
        for v in [c.anchor for c in s.circles] + list(s.intervals):
            graph.join(base_vertex[i], component[v])
            graph_edges += 1
    graph_components = len({graph.find(v) for v in range(len(graph.parent))})
    cycle_rank = graph_edges - len(graph.parent) + graph_components
    orientable = [i for i, s in enumerate(model.surfaces) if s.saturated and s.orientable]
    twisted = [i for i, s in enumerate(model.surfaces) if s.saturated and not s.orientable]
    d, t = len(generators), len(twisted)
    columns = []
    for face in core.faces:
        chain = loop_chain(core, face)
        columns.append([chain[e] for e in generators] + [0] * t)
    for i in orientable + twisted:
        total = [0] * d
        for c in model.surfaces[i].circles:
            chain = loop_chain(core, c)
            for j, e in enumerate(generators):
                total[j] += chain[e]
        column = total + [0] * t
        if i in twisted:
            column[d + twisted.index(i)] = 2
        columns.append(column)
    matrix = tuple(tuple(col[r] for col in columns) for r in range(d + t))
    free = cycle_rank
    twos = 0
    b0 = graph_components
    euler = core.vertices - len(core.edges) + len(core.faces) - core.three_cells
    local_free = []
    for s in model.surfaces:
        c = len(s.circles)
        if s.boundary == 0:
            local = 2 * s.complexity if s.orientable else s.complexity - 1
            if not s.orientable:
                twos += s.multiplicity
        elif s.saturated:
            local = 2 * s.complexity if s.orientable else s.complexity - 1
        else:
            local = (2 if s.orientable else 1) * s.complexity + s.boundary - 1 - c
        local_free.append(local)
        free += s.multiplicity * local
        if not s.attached:
            b0 += s.multiplicity
        euler += s.multiplicity * s.chi - len(s.intervals)
    return Condensation(
        "bounded-interface-homology-v1", fingerprint(model), matrix, len(columns),
        tuple(generators), tuple(tree), component, tuple(orientable), tuple(twisted),
        len(graph.parent), graph_edges, graph_components, cycle_rank,
        free, twos, b0, euler, tuple(local_free))
