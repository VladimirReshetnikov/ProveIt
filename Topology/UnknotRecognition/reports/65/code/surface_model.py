"""Independent literal PL surface oracle for small tests.

Each partition block is realized by a polygonal disk with separated boundary
edges for its ports. Triangulated polygons are glued at the requested edges.
Vertex links, Euler characteristics, boundary circles and orientability are
computed from the resulting simplicial complex, not from partition ranks.
This does not certify an embedding in a knot exterior.
"""
from __future__ import annotations
from collections import defaultdict


def assemble_patches(parts, pairings, twists=None):
    if twists is None:
        twists = [0] * len(pairings)
    if len(twists) != len(pairings) or any(type(x) is not int or x not in (0, 1) for x in twists):
        raise ValueError("invalid twists")
    if sum(len(p) for p in parts) > 20000:
        raise ValueError("literal oracle size cap")
    triangles = []
    ports = {}
    nvertices = 0
    for j, p in enumerate(parts):
        if not p or any(type(x) is not int or x < 0 for x in p):
            raise ValueError("invalid patch partition")
        blocks = defaultdict(list)
        for i, a in enumerate(p):
            blocks[a].append(i)
        for block in blocks.values():
            k = len(block)
            ring = list(range(nvertices, nvertices + 4 * k))
            center = nvertices + 4 * k
            nvertices = center + 1
            for i in range(4 * k):
                triangles.append((center, ring[i], ring[(i + 1) % (4 * k)]))
            for i, port in enumerate(block):
                ports[(j, port)] = (ring[4 * i], ring[4 * i + 1])
    parent = list(range(nvertices))
    def find(a):
        while parent[a] != a:
            a = parent[a]
        return a
    def unite(a, b):
        a, b = find(a), find(b)
        if a != b:
            parent[a] = b
    used = set()
    for (left, right), twist in zip(pairings, twists):
        left, right = tuple(left), tuple(right)
        if left == right or left in used or right in used or left not in ports or right not in ports:
            raise ValueError("a port must be paired at most once")
        used.update((left, right))
        a, b = ports[left]
        c, d = ports[right]
        if not twist:
            c, d = d, c  # opposite boundary orientations
        unite(a, c)
        unite(b, d)
    tris = [tuple(find(v) for v in tri) for tri in triangles]
    if any(len(set(t)) != 3 for t in tris) or len({tuple(sorted(t)) for t in tris}) != len(tris):
        raise ValueError("not a simplicial triangulation")
    edges = defaultdict(list)
    links = defaultdict(list)
    for i, tri in enumerate(tris):
        for j in range(3):
            a, b = tri[j], tri[(j + 1) % 3]
            edges[tuple(sorted((a, b)))].append((i, int(a < b)))
            v = tri[j]
            links[v].append((tri[(j + 1) % 3], tri[(j + 2) % 3]))
    if any(len(ts) > 2 for ts in edges.values()):
        raise ValueError("nonmanifold edge")
    for v, link_edges in links.items():
        adj = defaultdict(list)
        for a, b in link_edges:
            adj[a].append(b)
            adj[b].append(a)
        degrees = [len(ns) for ns in adj.values()]
        if any(x not in (1, 2) for x in degrees) or degrees.count(1) not in (0, 2):
            raise ValueError("nonmanifold vertex link")
        seen = set()
        todo = [next(iter(adj))]
        while todo:
            a = todo.pop()
            if a not in seen:
                seen.add(a)
                todo.extend(adj[a])
        if len(seen) != len(adj):
            raise ValueError("disconnected vertex link")
    adjacent = defaultdict(list)
    for incidences in edges.values():
        if len(incidences) == 2:
            (i, d), (j, e) = incidences
            adjacent[i].append((j, int(d == e)))
            adjacent[j].append((i, int(d == e)))
    unseen = set(range(len(tris)))
    result = []
    while unseen:
        start = min(unseen)
        phase, todo = {start: 0}, [start]
        orientable = True
        while todo:
            i = todo.pop()
            for j, parity in adjacent[i]:
                expected = phase[i] ^ parity
                if j in phase and phase[j] != expected:
                    orientable = False
                elif j not in phase:
                    phase[j] = expected
                    todo.append(j)
        comp = set(phase)
        unseen -= comp
        vs = {v for i in comp for v in tris[i]}
        es = {e for e, inc in edges.items() if inc[0][0] in comp}
        chi = len(vs) - len(es) + len(comp)
        boundary = defaultdict(list)
        for a, b in es:
            if len(edges[(a, b)]) == 1:
                boundary[a].append(b)
                boundary[b].append(a)
        if any(len(ns) != 2 for ns in boundary.values()):
            raise ValueError("boundary is not a 1-manifold")
        pending = set(boundary)
        circles = 0
        while pending:
            circles += 1
            todo = [min(pending)]
            while todo:
                v = todo.pop()
                if v in pending:
                    pending.remove(v)
                    todo.extend(boundary[v])
        result.append({"chi": chi, "boundary_circles": circles,
                       "orientable": orientable, "triangles": len(comp)})
    return {"components": result, "component_count": len(result),
            "chi": sum(x["chi"] for x in result),
            "is_disk": len(result) == 1 and result[0]["chi"] == 1
                       and result[0]["boundary_circles"] == 1 and result[0]["orientable"],
            "triangle_count": len(tris)}


def glue_two(p, q, twists=None):
    if len(p) != len(q):
        raise ValueError("different widths")
    return assemble_patches([p, q], [((0, i), (1, i)) for i in range(len(p))], twists)
