"""Bounded alternative tree gauges without repeating cohomology elimination.

Every candidate is cohomologous to the supplied cocycle and vanishes on
its BFS tree. A primitive rank-one input therefore gives connected surfaces.
This producer does not certify those hypotheses; positive source proofs
still pass the independent cocycle verifier.
"""
from random import Random

from .integer_codec import encoded_integer
from .normal_cocycle import local_coordinates
from .normal_surface_geometry import _prepare, _coordinates, _EDGES, NormalOrbitError


def cocycle_tree_candidates(triangulation, heights, *, trials=4, check=lambda: None):
    """Yield trial metadata and each distinct candidate, with bounded storage.

    Try highest-degree roots first, ordered by vertex label on ties. Trials
    after the first four shuffle adjacency with a fixed local random seed.
    Potentials are normalized at the smallest vertex, making duplicate
    detection invariant under the choice of BFS root's additive constant.
    """
    if type(trials) is not int or trials < 0:
        raise ValueError('tree trials must be a nonnegative integer')
    check()
    if trials == 0:
        return
    p = _prepare(triangulation, check)
    yield from _prepared_tree_candidates(p, heights, trials=trials, check=check)


def _prepared_tree_candidates(p, heights, *, trials, check):
    """Internal discovery on geometry already validated in this search."""
    if type(heights) is not list or len(heights) != len(p['tetrahedra']):
        raise ValueError('expected one height row per tetrahedron')
    h, edges = [], {}
    for t, row in enumerate(heights):
        check()
        if type(row) is not list or len(row) != 4:
            raise ValueError('expected four integer heights per tetrahedron')
        row = [encoded_integer(x) for x in row]
        h.append(row)
        for j, (a, b) in enumerate(_EDGES):
            local = 6*t+j
            u, v = p['vertex_roots'][4*t+a], p['vertex_roots'][4*t+b]
            value = row[b]-row[a]
            if p['edge_orientations'][local]:
                u, v, value = v, u, -value
            edge = p['edge_roots'][local]
            if edge in edges and edges[edge] != (u, v, value):
                raise NormalOrbitError('height differences do not define a global cocycle')
            edges[edge] = u, v, value
    vertices = [p['vertex_roots'][4*t:4*t+4] for t in range(len(h))]
    adjacency = {v: [] for v in p['vertex_roots']}
    for edge, (u, v, value) in edges.items():
        check()
        if u != v:
            adjacency[u].append((v, value, edge))
            adjacency[v].append((u, -value, edge))
    labels = sorted(adjacency)
    roots = sorted(labels, key=lambda v: (-len(adjacency[v]), v))
    seen = {tuple(0 for v in labels)}
    rng = Random(261009471)
    for trial in range(trials):
        check()
        root = roots[trial % len(roots)]
        neighbors = {}
        for v, arcs in adjacency.items():
            check()
            neighbors[v] = list(arcs)
            if trial >= 4:
                rng.shuffle(neighbors[v])
        potential, queue = {root: 0}, [root]
        for u in queue:
            check()
            for v, value, edge in neighbors[u]:
                check()
                if v not in potential:
                    potential[v] = potential[u]+value
                    queue.append(v)
        if len(potential) != len(labels):
            raise NormalOrbitError('cocycle edge graph is disconnected')
        offset = potential[labels[0]]
        signature = tuple(potential[v]-offset for v in labels)
        metadata = dict(trial=trial+1, root=root, randomized=trial >= 4,
                        duplicate=signature in seen)
        if metadata['duplicate']:
            yield metadata
            continue
        seen.add(signature)
        adjusted, coordinates = [], []
        for vs, hs in zip(vertices, h):
            check()
            row = [height-potential[v]+offset for height, v in zip(hs, vs)]
            adjusted.append(row)
            coordinates.append(local_coordinates(row))
        analysed = _coordinates(p, coordinates, check)
        yield dict(**metadata, heights=adjusted, coordinates=coordinates,
                   euler_characteristic=analysed['euler_characteristic'],
                   normal_pieces=analysed['normal_disks'])
