"""Small, independent simplicial-surface geometry for local integration tests.

Not a triangulated-three-manifold or ambient-embedding verifier. Surfaces must
be genuine finite simplicial complexes, not arbitrary generalized triangulations.
The deliberately narrow contract rejects unsupported identifications.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import defaultdict
from typing import Sequence
from .core import SignedPartition


def edge(a: int, b: int) -> tuple[int, int]:
    return (a, b) if a < b else (b, a)


def direction(a: int, b: int) -> int:
    return 0 if a < b else 1


@dataclass(frozen=True, slots=True)
class Surface:
    triangles: tuple[tuple[int, int, int], ...]
    seams: tuple[tuple[int, ...], ...] = ()


@dataclass(frozen=True, slots=True)
class SurfaceInfo:
    euler: int
    components: int
    orientable: bool
    boundary_components: int
    signature: SignedPartition | None
    seam_types: tuple[str, ...]
    component_euler: tuple[int, ...]
    triangle_component: tuple[int, ...]
    triangle_orientation: tuple[int, ...]

    @property
    def is_disk(self) -> bool:
        return (self.components == 1 and self.orientable and
                self.boundary_components > 0 and self.euler == 1)


def inspect(surface: Surface, *, require_live: bool = True) -> SurfaceInfo:
    """Validate links, propagate orientations, and compute owned cell counts.

    A seam is an ordered boundary edge path. A circle repeats its first vertex;
    distinct seams must have disjoint vertex sets. Seam offsets record whether
    the induced boundary orientation agrees with the supplied path direction.
    """
    tris = surface.triangles
    if not tris:
        raise ValueError("empty surfaces are outside this interface")
    faces = set()
    incidences = defaultdict(list)
    vertices = set()
    vertex_links = defaultdict(list)
    for t, face in enumerate(tris):
        if type(face) is not tuple or len(face) != 3 or any(type(v) is not int for v in face):
            raise ValueError("triangles must be triples of exact integers")
        if len(set(face)) != 3 or frozenset(face) in faces:
            raise ValueError("degenerate or duplicated face")
        faces.add(frozenset(face)); vertices.update(face)
        a, b, c = face
        for u, v in ((a, b), (b, c), (c, a)):
            incidences[edge(u, v)].append((t, direction(u, v)))
        for v, x, y in ((a, b, c), (b, c, a), (c, a, b)):
            vertex_links[v].append(edge(x, y))
    if any(len(x) > 2 for x in incidences.values()):
        raise ValueError("nonmanifold edge")
    for v, link_edges in vertex_links.items():
        adj = defaultdict(set)
        for a, b in link_edges:
            adj[a].add(b); adj[b].add(a)
        todo = [next(iter(adj))]; reached = set(todo)
        while todo:
            for x in adj[todo.pop()]:
                if x not in reached:
                    reached.add(x); todo.append(x)
        degrees = [len(x) for x in adj.values()]
        if len(reached) != len(adj) or any(d not in (1, 2) for d in degrees) or degrees.count(1) not in (0, 2):
            raise ValueError(f"nonmanifold vertex link at {v}")
    adj = [[] for _ in tris]
    for inc in incidences.values():
        if len(inc) == 2:
            (a, da), (b, db) = inc
            parity = da ^ db ^ 1  # induced edge orientations must oppose
            adj[a].append((b, parity)); adj[b].append((a, parity))
    comp = [-1] * len(tris); orientation = [-1] * len(tris)
    orientable = True; ncomp = 0
    for t in range(len(tris)):
        if comp[t] >= 0:
            continue
        comp[t] = ncomp; orientation[t] = 0; todo = [t]
        while todo:
            u = todo.pop()
            for v, parity in adj[u]:
                value = orientation[u] ^ parity
                if comp[v] < 0:
                    comp[v] = ncomp; orientation[v] = value; todo.append(v)
                elif orientation[v] != value:
                    orientable = False
        ncomp += 1
    boundary_adj = defaultdict(set)
    for (a, b), inc in incidences.items():
        if len(inc) == 1:
            boundary_adj[a].add(b); boundary_adj[b].add(a)
    if any(len(v) != 2 for v in boundary_adj.values()):
        raise ValueError("boundary is not a union of circles")
    boundary_count = 0; reached = set()
    for v in boundary_adj:
        if v in reached:
            continue
        boundary_count += 1; todo = [v]; reached.add(v)
        while todo:
            for u in boundary_adj[todo.pop()]:
                if u not in reached:
                    todo.append(u); reached.add(u)
    component_euler = [0] * ncomp
    vertex_owner = {}; edge_owner = {}
    for t, (a, b, c) in enumerate(tris):
        k = comp[t]; component_euler[k] += 1
        for v in (a, b, c):
            vertex_owner[v] = k
        for e in (edge(a, b), edge(b, c), edge(c, a)):
            edge_owner[e] = k
    for k in vertex_owner.values():
        component_euler[k] += 1
    for k in edge_owner.values():
        component_euler[k] -= 1
    used = set(); labels = []; offsets = []; seam_types = []
    for seam in surface.seams:
        if type(seam) is not tuple or len(seam) < 2 or any(type(v) is not int for v in seam):
            raise ValueError("invalid seam path")
        circular = seam[0] == seam[-1]
        body = seam[:-1] if circular else seam
        if len(set(body)) != len(body) or (circular and len(body) < 3):
            raise ValueError("seam is not embedded")
        if set(body) & used:
            raise ValueError("seams are not pairwise disjoint")
        used.update(body)
        signature = None
        for a, b in zip(seam, seam[1:]):
            inc = incidences.get(edge(a, b), [])
            if len(inc) != 1:
                raise ValueError("seam not on boundary")
            t, triangle_direction = inc[0]
            current = (comp[t], orientation[t] ^ triangle_direction ^ direction(a, b))
            if signature is None:
                signature = current
            elif signature != current:
                raise ValueError("incoherent boundary seam")
        assert signature is not None
        labels.append(signature[0]); offsets.append(signature[1])
        seam_types.append("circle" if circular else "arc")
    if require_live and set(labels) != set(range(ncomp)):
        raise ValueError("a component has no live seam")
    signed = SignedPartition.canonical(labels, offsets) if labels and orientable else None
    return SurfaceInfo(sum(component_euler), ncomp, orientable, boundary_count, signed,
                       tuple(seam_types), tuple(component_euler), tuple(comp), tuple(orientation))


def glue(left: Surface, right: Surface, *, reverse: Sequence[bool] | None = None) -> Surface:
    """Glue corresponding paths and return a genuine simplicial quotient.

    Reverse=True reverses that right path before matching; by default paths
    are matched pointwise. Orientation signs are checked on the resulting mesh.
    """
    li, ri = inspect(left), inspect(right)
    if li.seam_types != ri.seam_types:
        raise ValueError("different seam types")
    if reverse is None:
        reverse = [False] * len(left.seams)
    if len(reverse) != len(left.seams) or any(type(x) is not bool for x in reverse):
        raise ValueError("one Boolean reversal per seam required")
    all_vertices = [(0, v) for v in sorted({v for f in left.triangles for v in f})]
    all_vertices += [(1, v) for v in sorted({v for f in right.triangles for v in f})]
    ids = {x: i for i, x in enumerate(all_vertices)}; parent = list(range(len(ids)))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for a, b, rev in zip(left.seams, right.seams, reverse):
        if len(a) != len(b):
            raise ValueError("different seam subdivisions")
        if rev:
            b = tuple(reversed(b))
        for u, v in zip(a, b):
            x, y = find(ids[(0, u)]), find(ids[(1, v)])
            parent[y] = x
    new_ids = {}; triangles = []
    for side, mesh in enumerate((left, right)):
        for face in mesh.triangles:
            out = []
            for v in face:
                root = find(ids[(side, v)])
                if root not in new_ids:
                    new_ids[root] = len(new_ids)
                out.append(new_ids[root])
            triangles.append(tuple(out))
    out = Surface(tuple(triangles))
    inspect(out, require_live=False)
    return out


def adjusted_completion(info: SurfaceInfo, reverse: Sequence[bool]) -> SignedPartition:
    """Convert boundary directions into the left-side orientation convention.

    A nonreversed gluing requires opposite boundary directions; reversing a
    path flips this relation. The uniform opposite flip cancels on each block,
    so it suffices to gauge by the per-seam reversal bits.
    """
    if info.signature is None:
        raise ValueError("completion is not orientable or has no seams")
    return info.signature.gauge(tuple(int(x) for x in reverse))


def fan_disk(n: int, *, seams: tuple[tuple[int, ...], ...] = ()) -> Surface:
    if type(n) is not int or n < 3:
        raise ValueError("at least three boundary edges required")
    return Surface(tuple((n, i, (i + 1) % n) for i in range(n)), seams)


def annulus(n: int = 6) -> Surface:
    if type(n) is not int or n < 4:
        raise ValueError("annulus subdivision too small")
    tris = []
    for i in range(n):
        j = (i + 1) % n
        tris.extend(((i, j, n + j), (i, n + j, n + i)))
    return Surface(tuple(tris), (tuple(range(n, 2 * n)) + (n,),))


def punctured_torus(n: int = 4) -> Surface:
    if type(n) is not int or n < 4:
        raise ValueError("torus grid too small")
    def v(i, j): return (i % n) * n + (j % n)
    tris = []
    for i in range(n):
        for j in range(n):
            tris.extend(((v(i,j), v(i+1,j), v(i+1,j+1)),
                         (v(i,j), v(i+1,j+1), v(i,j+1))))
    removed = tris.pop(0)
    return Surface(tuple(tris), ((removed[0], removed[1]),))


def planar_holes() -> Surface:
    """A rectangular triangulated pair of pants with two square circle seams."""
    width, height = 7, 4
    def v(i,j): return j * (width + 1) + i
    holes = {(2,1), (4,1)}; tris = []
    for j in range(height):
        for i in range(width):
            if (i,j) in holes:
                continue
            tris.extend(((v(i,j), v(i+1,j), v(i+1,j+1)),
                         (v(i,j), v(i+1,j+1), v(i,j+1))))
    seams = tuple((v(i,j), v(i+1,j), v(i+1,j+1), v(i,j+1), v(i,j))
                  for i,j in sorted(holes))
    return Surface(tuple(tris), seams)


def disjoint_surfaces(items: Sequence[Surface]) -> Surface:
    tris = []; seams = []; offset = 0
    for item in items:
        vertices = sorted({v for f in item.triangles for v in f})
        ids = {v: offset + i for i, v in enumerate(vertices)}
        offset += len(vertices)
        tris.extend(tuple(ids[v] for v in f) for f in item.triangles)
        seams.extend(tuple(ids[v] for v in s) for s in item.seams)
    return Surface(tuple(tris), tuple(seams))


def barycentric_subdivision(surface: Surface) -> Surface:
    """Six triangles per old triangle; subdivide all marked paths compatibly."""
    inspect(surface,require_live=False)
    vertices=sorted({v for f in surface.triangles for v in f}); ids={v:i for i,v in enumerate(vertices)}
    edge_ids={}; next_id=len(ids)
    for f in surface.triangles:
        for a,b in ((f[0],f[1]),(f[1],f[2]),(f[2],f[0])):
            e=edge(a,b)
            if e not in edge_ids:
                edge_ids[e]=next_id;next_id+=1
    tris=[]
    for a,b,c in surface.triangles:
        center=next_id;next_id+=1
        for u,v in ((a,b),(b,c),(c,a)):
            mid=edge_ids[edge(u,v)]
            tris.extend(((ids[u],mid,center),(mid,ids[v],center)))
    seams=[]
    for path in surface.seams:
        out=[ids[path[0]]]
        for a,b in zip(path,path[1:]):
            out.extend((edge_ids[edge(a,b)],ids[b]))
        seams.append(tuple(out))
    return Surface(tuple(tris),tuple(seams))


def realize_partition(partition: SignedPartition) -> Surface:
    """Realize every signed state by a union of oriented fan disks.

    This proves realizability by abstract surface fragments, not by prescribed
    disjoint normal patches in an ambient triangulated three-manifold.
    """
    tris=[];seams=[None]*partition.r;offset=0
    for k in range(partition.blocks):
        ports=[i for i,a in enumerate(partition.labels) if a==k]
        n=3*len(ports)+3
        disk=fan_disk(n)
        tris.extend(tuple(v+offset for v in f) for f in disk.triangles)
        for j,i in enumerate(ports):
            path=(offset+3*j,offset+3*j+1)
            seams[i]=tuple(reversed(path)) if partition.offsets[i] else path
        offset+=n+1
    out=Surface(tuple(tris),tuple(seams))
    assert inspect(out).signature==partition
    return out
