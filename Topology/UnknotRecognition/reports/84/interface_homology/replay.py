"""Independent presentation replay: graph traversal, not the producer's DSU.

The replay authenticates the algebraic interface result, not source geometry.
A separate interface-extraction checker must bind it to a normal-cut packet.
"""
from __future__ import annotations
from .model import Model, validate, fingerprint
from .condense import Condensation


def _components(n: int, edges: list[tuple[int, int]]) -> tuple[list[int], int]:
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    labels = [-1] * n
    count = 0
    for v in range(n):
        if labels[v] != -1:
            continue
        labels[v] = count
        stack = [v]
        while stack:
            for w in adj[stack.pop()]:
                if labels[w] == -1:
                    labels[w] = count
                    stack.append(w)
        count += 1
    return labels, count


def verify_condensation(model: Model, packet: Condensation) -> bool:
    try:
        validate(model)
        if not isinstance(packet, Condensation):
            return False
        if packet.schema != "bounded-interface-homology-v1" or packet.source_sha256 != fingerprint(model):
            return False
        scalar_fields = ('relation_count', 'graph_vertices', 'graph_edges',
                         'graph_components', 'graph_cycle_rank', 'free_bulk',
                         'two_torsion_bulk', 'b0', 'euler')
        if any(type(getattr(packet, key)) is not int for key in scalar_fields):
            return False
        if any(type(x) is not int for field in (packet.surface_free,
               packet.saturated_orientable, packet.saturated_nonorientable) for x in field):
            return False
        core = model.core
        tree, non = list(packet.core_forest), list(packet.core_generators)
        if any(type(i) is not int for i in tree + non):
            return False
        if len(set(tree + non)) != len(tree + non) or sorted(tree + non) != list(range(len(core.edges))):
            return False
        labels, k = _components(core.vertices, list(core.edges))
        forest_labels, f = _components(core.vertices, [core.edges[i] for i in tree])
        if len(tree) != core.vertices - k or f != k:
            return False
        if any(forest_labels[u] != forest_labels[v] for u, v in core.edges):
            return False
        supplied = packet.core_component
        if len(supplied) != core.vertices or any(type(x) is not int for x in supplied):
            return False
        # Allow any consistent dense component labelling; no DSU dependence.
        mapping = {}
        for a, b in zip(labels, supplied):
            if a in mapping and mapping[a] != b:
                return False
            mapping[a] = b
        if sorted(mapping.values()) != list(range(k)):
            return False
        ported = [i for i, s in enumerate(model.surfaces) if s.attached]
        gv = k + len(ported)
        edges = []
        for j, i in enumerate(ported):
            s = model.surfaces[i]
            edges.extend((k+j, supplied[c.anchor]) for c in s.circles)
            edges.extend((k+j, supplied[v]) for v in s.intervals)
        _, gc = _components(gv, edges)
        gr = len(edges) - gv + gc
        if (packet.graph_vertices, packet.graph_edges, packet.graph_components, packet.graph_cycle_rank) != (gv, len(edges), gc, gr):
            return False
        ori = tuple(i for i, s in enumerate(model.surfaces) if s.saturated and s.orientable)
        nonori = tuple(i for i, s in enumerate(model.surfaces) if s.saturated and not s.orientable)
        if packet.saturated_orientable != ori or packet.saturated_nonorientable != nonori:
            return False
        d, t = len(non), len(nonori)
        # Exponent sums are independently extracted directly from signed words.
        position = {e+1: j for j, e in enumerate(non)}
        def vector(words):
            result = [0] * (d+t)
            for word in words:
                for a in word:
                    if abs(a) in position:
                        result[position[abs(a)]] += (a > 0) - (a < 0)
            return result
        cols = [vector([face.word]) for face in core.faces]
        for i in ori:
            cols.append(vector([c.word for c in model.surfaces[i].circles]))
        for j, i in enumerate(nonori):
            v = vector([c.word for c in model.surfaces[i].circles])
            v[d+j] = 2
            cols.append(v)
        expected = tuple(tuple(c[r] for c in cols) for r in range(d+t))
        if packet.matrix != expected or packet.relation_count != len(cols):
            return False
        if any(type(x) is not int for row in packet.matrix for x in row):
            return False
        local, free, twos, count = [], gr, 0, gc
        chi = core.vertices - len(core.edges) + len(core.faces) - core.three_cells
        for s in model.surfaces:
            handles = (2 if s.orientable else 1) * s.complexity
            if s.boundary and not s.saturated:
                rank = handles + s.boundary - len(s.circles) - 1
            else:
                rank = handles - int(not s.orientable)
            local.append(rank)
            free += s.multiplicity * rank
            if not s.boundary and not s.orientable:
                twos += s.multiplicity
            if not s.attached:
                count += s.multiplicity
            chi += s.multiplicity * (2-handles-s.boundary) - len(s.intervals)
        return (packet.surface_free == tuple(local) and
                (packet.free_bulk, packet.two_torsion_bulk, packet.b0, packet.euler) == (free, twos, count, chi) and
                all(type(x) is int for x in (packet.free_bulk, packet.two_torsion_bulk, packet.b0, packet.euler, packet.relation_count)))
    except (ValueError, TypeError, IndexError, KeyError, AttributeError):
        return False
