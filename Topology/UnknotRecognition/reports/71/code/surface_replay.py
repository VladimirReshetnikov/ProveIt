"""Literal polygon/triangle replay, independent of frontier and cycle algebra.

This validates abstract PL surfaces only. It has no knot-exterior embedding data.
Each label is represented by one separated boundary edge of a polygonal disk.
"""
from collections import defaultdict, deque


class Equivalence:
    def __init__(self, n):
        self.names = list(range(n))
    def root(self, x):
        while self.names[x] != x:
            x = self.names[x]
        return x
    def identify(self, x, y):
        a, b = self.root(x), self.root(y)
        if a != b:
            self.names[max(a, b)] = min(a, b)


def _components(nodes, edges):
    adjacency = {v: set() for v in nodes}
    for a, b in edges:
        adjacency[a].add(b); adjacency[b].add(a)
    unseen, groups = set(nodes), []
    while unseen:
        todo, group = [min(unseen)], set()
        while todo:
            x = todo.pop()
            if x in group:
                continue
            group.add(x); unseen.discard(x)
            todo.extend(adjacency[x] - group)
        groups.append(group)
    return groups


def replay(partitions, seams):
    """seam = (piece_a, arc_a, piece_b, arc_b, reversed_endpoints: bool)."""
    faces, arcs, n = [], {}, 0
    for piece, p in enumerate(partitions):
        for block in sorted(set(p)):
            labels = [i for i, b in enumerate(p) if b == block]
            k = len(labels)
            boundary = list(range(n, n + 4 * k))
            center = n + 4 * k
            n += 4 * k + 1
            for j, v in enumerate(boundary):
                faces.append((center, v, boundary[(j + 1) % len(boundary)]))
            for j, label in enumerate(labels):
                arcs[piece, label] = (boundary[4 * j], boundary[4 * j + 1])
    eq = Equivalence(n)
    used = set()
    for a, i, b, j, reverse in seams:
        if (a, i) in used or (b, j) in used or (a, i) == (b, j):
            raise ValueError('attachment arc reused')
        used.update(((a, i), (b, j)))
        x, y = arcs[a, i], arcs[b, j]
        if reverse:
            y = y[::-1]
        eq.identify(x[0], y[0]); eq.identify(x[1], y[1])
    faces = [tuple(eq.root(v) for v in face) for face in faces]
    if any(len(set(f)) != 3 for f in faces):
        raise ValueError('degenerate quotient triangle')
    vertices = {v for f in faces for v in f}
    edges = defaultdict(list)
    links = defaultdict(list)
    for i, f in enumerate(faces):
        for j in range(3):
            a, b, c = f[j], f[(j + 1) % 3], f[(j + 2) % 3]
            edges[tuple(sorted((a, b)))].append((i, 1 if a < b else -1))
            links[a].append((b, c))
    if any(len(inc) not in (1, 2) for inc in edges.values()):
        raise ValueError('nonmanifold edge')
    for v, pairs in links.items():
        nodes = {x for e in pairs for x in e}
        degree = {x: 0 for x in nodes}
        for a, b in pairs:
            degree[a] += 1; degree[b] += 1
        degrees = list(degree.values())
        if len(_components(nodes, pairs)) != 1 or any(d not in (1, 2) for d in degrees) or degrees.count(1) not in (0, 2):
            raise ValueError('nonmanifold vertex link')
    boundary_edges = [e for e, inc in edges.items() if len(inc) == 1]
    boundary_nodes = {v for e in boundary_edges for v in e}
    boundary_components = _components(boundary_nodes, boundary_edges)
    groups = _components(vertices, edges)
    # Propagate orientation signs on adjacent triangles.
    adjacency = [[] for _ in faces]
    for inc in edges.values():
        if len(inc) == 2:
            (a, da), (b, db) = inc
            relation = -da * db
            adjacency[a].append((b, relation)); adjacency[b].append((a, relation))
    signs, orientable = {}, True
    for first in range(len(faces)):
        if first in signs:
            continue
        signs[first] = 1
        todo = [first]
        while todo:
            a = todo.pop()
            for b, relation in adjacency[a]:
                wanted = signs[a] * relation
                if b in signs and signs[b] != wanted:
                    orientable = False
                elif b not in signs:
                    signs[b] = wanted; todo.append(b)
    chi = len(vertices) - len(edges) + len(faces)
    return {'vertices': len(vertices), 'edges': len(edges), 'triangles': len(faces),
            'components': len(groups), 'euler': chi, 'boundary_components': len(boundary_components),
            'orientable': orientable, 'manifold': True,
            'disk': len(groups) == 1 and chi == 1 and len(boundary_components) == 1 and orientable}


def replay_pair(p, q, reverse=True):
    if len(p) != len(q):
        raise ValueError('mismatched interface')
    return replay([p, q], [(0, i, 1, i, reverse) for i in range(len(p))])


def replay_witness(g, witness):
    if len(witness) != len(g.layers) + 2:
        raise ValueError('wrong witness length')
    selected = [g.initial[witness[0]].partition]
    selected.extend(g.layers[i][witness[i + 1]].partition for i in range(len(g.layers)))
    selected.append(g.caps[witness[-1]].partition)
    seams = []
    for i, width in enumerate(g.widths):
        previous_start = 0 if i == 0 else g.widths[i - 1]
        for e in range(width):
            seams.append((i, previous_start + e, i + 1, e, True))
    return replay(selected, seams)
