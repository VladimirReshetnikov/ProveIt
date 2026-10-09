"""Literal finite triangulated surfaces, for small independent topology audits.

Each partition block is a triangulated polygonal disc. Its labelled boundary
edges are separated by two unused edges. A quotient identifies seam edges
with reversed orientations. The oracle counts simplices, checks vertex links,
and computes component Euler characteristic and boundary-circle counts.
It does not embed these abstract surfaces in a three-manifold.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass


class Union:
    def __init__(self, n):
        self.p = list(range(n))
    def root(self, x):
        while self.p[x] != x:
            x = self.p[x]
        return x
    def join(self, x, y):
        self.p[self.root(x)] = self.root(y)


@dataclass
class Mesh:
    vertices: int
    triangles: list[tuple[int, int, int]]
    arcs: dict[tuple[int, int], tuple[int, int]]


def make_pieces(partition_list):
    triangles, arcs = [], {}
    nv = 0
    for piece, p in enumerate(partition_list):
        for block in range(max(p) + 1):
            labels = [i for i, a in enumerate(p) if a == block]
            k = len(labels)
            perimeter = list(range(nv, nv + 3*k))
            center = nv + 3*k
            nv += 3*k + 1
            for i in range(3*k):
                triangles.append((center, perimeter[i], perimeter[(i+1) % (3*k)]))
            for j, label in enumerate(labels):
                arcs[(piece, label)] = (perimeter[3*j], perimeter[3*j+1])
    return Mesh(nv, triangles, arcs)


def replay(partition_list, seams):
    mesh = make_pieces(partition_list)
    uf = Union(mesh.vertices)
    consumed = set()
    for left, right in seams:
        if left in consumed or right in consumed or left == right:
            raise ValueError("a marked interval is used more than once")
        consumed.update((left, right))
        a, b = mesh.arcs[left]
        c, d = mesh.arcs[right]
        uf.join(a, d)
        uf.join(b, c)
    tris = [tuple(uf.root(v) for v in tri) for tri in mesh.triangles]
    if any(len(set(t)) != 3 for t in tris) or len(set(tuple(sorted(t)) for t in tris)) != len(tris):
        raise ValueError("quotient is not a simplicial surface")
    edges = defaultdict(list)
    for i, tri in enumerate(tris):
        for j in range(3):
            a, b = tri[j], tri[(j+1) % 3]
            edges[tuple(sorted((a, b)))].append((i, a, b))
    if any(len(v) > 2 for v in edges.values()):
        raise ValueError("nonmanifold edge")
    # Every vertex link must be a path or a cycle, and connected.
    link_edges = defaultdict(list)
    for tri in tris:
        for j, v in enumerate(tri):
            link_edges[v].append((tri[(j+1) % 3], tri[(j+2) % 3]))
    for v, pairs in link_edges.items():
        adj = defaultdict(list)
        for x, y in pairs:
            adj[x].append(y); adj[y].append(x)
        seen = set()
        stack = [next(iter(adj))]
        while stack:
            x = stack.pop()
            if x not in seen:
                seen.add(x); stack.extend(adj[x])
        degree_one = sum(len(neigh) == 1 for neigh in adj.values())
        if len(seen) != len(adj) or any(len(x) not in (1, 2) for x in adj.values()) or degree_one not in (0, 2):
            raise ValueError(f"invalid vertex link at {v}")
    components = Union(len(tris))
    for incidences in edges.values():
        if len(incidences) == 2:
            components.join(incidences[0][0], incidences[1][0])
            # Reversed seam identifications preserve these triangle orientations.
            _, a, b = incidences[0]
            _, c, d = incidences[1]
            if (a, b) != (d, c):
                raise ValueError("orientation mismatch")
    buckets = defaultdict(list)
    for i, tri in enumerate(tris):
        buckets[components.root(i)].append(i)
    result = []
    for ids in buckets.values():
        ids = set(ids)
        verts = {v for i in ids for v in tris[i]}
        local_edges = {e for e, inc in edges.items() if inc[0][0] in ids}
        boundary = [e for e in local_edges if len(edges[e]) == 1]
        badj = defaultdict(list)
        for a, b in boundary:
            badj[a].append(b); badj[b].append(a)
        if any(len(x) != 2 for x in badj.values()):
            raise ValueError("boundary is not a union of circles")
        seen = set(); circles = 0
        for v in badj:
            if v in seen:
                continue
            circles += 1; stack = [v]
            while stack:
                x = stack.pop()
                if x not in seen:
                    seen.add(x); stack.extend(badj[x])
        chi = len(verts) - len(local_edges) + len(ids)
        result.append({"vertices": len(verts), "edges": len(local_edges), "faces": len(ids),
                       "euler": chi, "boundary_circles": circles, "orientable": True,
                       "disk": chi == 1 and circles == 1})
    return {"components": result, "is_single_disk": len(result) == 1 and result[0]["disk"],
            "triangles": len(tris)}


def replay_pair(p, q):
    if len(p) != len(q):
        raise ValueError("pair width mismatch")
    return replay([p, q], [((0, i), (1, i)) for i in range(len(p))])


def replay_word(width, word, cap):
    # Keep every local atom, even a partial cyclic component; the mesh oracle
    # does not run the producer's pruning rule.
    if not word:
        word = [tuple(range(width)) * 2]
    pieces = list(word) + [cap]
    seams = []
    for j in range(len(word)-1):
        seams.extend(((j, width+i), (j+1, i)) for i in range(width))
    cap_id = len(word)
    seams.extend(((0, i), (cap_id, i)) for i in range(width))
    seams.extend(((len(word)-1, width+i), (cap_id, width+i)) for i in range(width))
    return replay(pieces, seams)
