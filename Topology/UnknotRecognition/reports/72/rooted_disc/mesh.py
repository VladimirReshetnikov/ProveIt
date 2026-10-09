"""Independent triangulated surface replay of abstract patch witnesses.

Good blocks are realized as disks, bad blocks as annuli. This independently
checks the abstraction, not embeddings into a 3-manifold. Charge labels are
formal additive data; no peripheral torus cocycles are inferred here.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from .kernel import State
from .assembly import Grammar


@dataclass(frozen=True)
class MeshResult:
    root_euler: int
    root_boundary_edges: int
    root_charge: int
    components: tuple[tuple[int, int, int], ...]  # Euler, boundary edges, charge
    triangles: int
    vertices: int
    edges: int
    cost: int

    def succeeds(self, target: int | None) -> bool:
        return self.root_euler == 1 and self.root_boundary_edges > 0 and (
            self.root_charge != 0 if target is None else self.root_charge == target)


class Mesh:
    def __init__(self):
        self.parent: list[int] = []
        self.triangles: list[tuple[int, int, int]] = []
        self.charges: dict[int, int] = {}

    def vertex(self) -> int:
        v = len(self.parent)
        self.parent.append(v)
        return v

    def find(self, v: int) -> int:
        root = v
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[v] != v:
            nxt = self.parent[v]
            self.parent[v] = root
            v = nxt
        return root

    def glue(self, a: tuple[int, int], b: tuple[int, int], reverse: bool = True) -> None:
        if reverse:
            b = b[::-1]
        for x, y in zip(a, b):
            self.parent[self.find(y)] = self.find(x)

    def fragment(self, partition, good, charges) -> tuple[list[tuple[int, int]], list[int]]:
        """Return boundary ports and one triangle id in each original component."""
        ports = [None] * len(partition)
        component_triangles = []
        for block, is_disk in enumerate(good):
            labels = [i for i, b in enumerate(partition) if b == block]
            n = max(3, 3 * len(labels))
            outer = [self.vertex() for _ in range(n)]
            first = len(self.triangles)
            component_triangles.append(first)
            if is_disk:
                center = self.vertex()
                self.triangles.extend((center, outer[i], outer[(i + 1) % n]) for i in range(n))
            else:
                inner = [self.vertex() for _ in range(n)]
                for i in range(n):
                    j = (i + 1) % n
                    self.triangles.append((outer[i], outer[j], inner[j]))
                    self.triangles.append((outer[i], inner[j], inner[i]))
            self.charges[first] = charges[block]
            for j, label in enumerate(labels):
                ports[label] = (outer[3 * j], outer[3 * j + 1])
        return ports, component_triangles

    def inspect(self, root_triangle: int, cost: int = 0) -> MeshResult:
        triangles = [tuple(self.find(v) for v in t) for t in self.triangles]
        if any(len(set(t)) != 3 for t in triangles) or len(set(tuple(sorted(t)) for t in triangles)) != len(triangles):
            raise ValueError("degenerate quotient triangles")
        edge_faces = defaultdict(list)
        vertex_links = defaultdict(list)
        for index, t in enumerate(triangles):
            a, b, c = t
            for x, y in ((a, b), (b, c), (c, a)):
                edge_faces[tuple(sorted((x, y)))].append(index)
            for x, y, z in ((a, b, c), (b, c, a), (c, a, b)):
                vertex_links[x].append((y, z))
        if any(len(faces) not in (1, 2) for faces in edge_faces.values()):
            raise ValueError("non-manifold edge")
        for link in vertex_links.values():
            graph = defaultdict(list)
            for a, b in link:
                graph[a].append(b); graph[b].append(a)
            if any(len(v) > 2 for v in graph.values()) or sum(len(v) == 1 for v in graph.values()) not in (0, 2):
                raise ValueError("non-manifold vertex degree")
            pending = [next(iter(graph))]; seen = set(pending)
            while pending:
                for w in graph[pending.pop()]:
                    if w not in seen:
                        seen.add(w); pending.append(w)
            if len(seen) != len(graph):
                raise ValueError("disconnected vertex link")
        adjacency = [set() for _ in triangles]
        for faces in edge_faces.values():
            if len(faces) == 2:
                a, b = faces
                adjacency[a].add(b); adjacency[b].add(a)
        remaining = set(range(len(triangles)))
        records, root_record = [], None
        while remaining:
            seed = min(remaining); component = {seed}; todo = [seed]
            while todo:
                for neighbor in adjacency[todo.pop()]:
                    if neighbor not in component:
                        component.add(neighbor); todo.append(neighbor)
            remaining -= component
            vertices = {v for i in component for v in triangles[i]}
            edges = {tuple(sorted((t[j], t[(j + 1) % 3]))) for i in component
                     for t in [triangles[i]] for j in range(3)}
            boundary = sum(len(edge_faces[e]) == 1 for e in edges)
            chi = len(vertices) - len(edges) + len(component)
            h = 0
            for i in component:
                h ^= self.charges.get(i, 0)
            record = (chi, boundary, h)
            records.append(record)
            if root_triangle in component:
                root_record = record
        if root_record is None:
            raise ValueError("missing distinguished triangle")
        return MeshResult(*root_record, tuple(records), len(triangles), len(vertex_links), len(edge_faces), cost)


def replay_pair(s: State, t: State, reversals: tuple[bool, ...] | None = None) -> MeshResult:
    if (s.r, s.q) != (t.r, t.q):
        raise ValueError("interface mismatch")
    if reversals is not None and len(reversals) != s.r:
        raise ValueError("one orientation choice per seam")
    mesh = Mesh()
    left, triangles = mesh.fragment(s.partition, s.good, s.charges)
    right, _ = mesh.fragment(t.partition, t.good, t.charges)
    for i, (a, b) in enumerate(zip(left, right)):
        mesh.glue(a, b, True if reversals is None else reversals[i])
    return mesh.inspect(triangles[0])


def replay_assignment(grammar: Grammar, witness: tuple[int, ...]) -> MeshResult:
    if len(witness) != 1 + len(grammar.layers) or any(type(i) is not int or i < 0 for i in witness):
        raise ValueError("invalid witness")
    if witness[0] >= len(grammar.initial) or any(witness[i + 1] >= len(layer) for i, layer in enumerate(grammar.layers)):
        raise ValueError("witness option is out of range")
    initial = grammar.initial[witness[0]]
    mesh = Mesh()
    ports, pieces = mesh.fragment(initial.state.partition, initial.state.good, initial.state.charges)
    root_triangle = pieces[0]
    live, cost = ports[1:], initial.cost  # marker edge 0 is never glued
    for i, layer in enumerate(grammar.layers):
        p = layer[witness[i + 1]]
        new_ports, _ = mesh.fragment(p.partition, p.good, p.charges)
        for a, b in zip(live, new_ports[:p.incoming]):
            mesh.glue(a, b)
        live = new_ports[p.incoming:]
        cost += p.cost
    if live:
        raise ValueError("unconsumed live ports")
    return mesh.inspect(root_triangle, cost)
