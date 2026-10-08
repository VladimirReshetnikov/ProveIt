"""Certified minimum-disc normal seeds within one integral cocycle class.

For tetrahedron t, the four local integer heights are h[t][i]. A potential f
on GLOBAL vertices changes them to h[t][i] + f[v[t][i]]. The number of normal
discs is the sum of the four-height spans. This module minimizes that sum by
exact min-cost flow. There are exactly as many unit augmentations as tetrahedra;
neither the network nor any loop expands a height or a normal coordinate.

An independent verifier checks a potential and a dual matching of tetrahedra
through shared vertices. Equality of their integer objectives proves optimality.
This is a restricted seed optimization, not a normal-surface enumeration or an
unknot recognizer. A one-vertex triangulation has no vertex-potential freedom.

Local normal-coordinate conventions agree with reports/02/unknotlab/normal.py:
tri0, tri1, tri2, tri3, quad01|23, quad02|13, quad03|12. The height-to-coordinate
construction is classical; the span optimization and its certificate are the
new research primitive here. The finite-triangulation adapter uses a protocol
and does not import any archived report or optional package.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Callable


QUAD_SIDES = (frozenset((0, 1)), frozenset((0, 2)), frozenset((0, 3)))


def _rows(rows, label):
    if not isinstance(rows, (tuple, list)) or not rows:
        raise ValueError(f'{label} must be a nonempty sequence of four-tuples')
    answer = []
    for row in rows:
        if (not isinstance(row, (tuple, list)) or len(row) != 4
                or any(type(value) is not int for value in row)):
            raise ValueError(f'{label} must contain four integers per tetrahedron')
        answer.append(tuple(row))
    return tuple(answer)


def _input(vertices, heights):
    vertices, heights = _rows(vertices, 'vertices'), _rows(heights, 'heights')
    if len(vertices) != len(heights):
        raise ValueError('vertices and heights must have the same number of rows')
    if any(v < 0 for row in vertices for v in row):
        raise ValueError('global vertex labels must be nonnegative integers')
    labels = tuple(sorted({v for row in vertices for v in row}))
    return vertices, heights, labels


def local_normal_coordinates(heights):
    """Seven binary coordinates from four local heights, using three gaps."""
    if (not isinstance(heights, (tuple, list)) or len(heights) != 4
            or any(type(h) is not int for h in heights)):
        raise ValueError('four integer local heights are required')
    order = sorted(range(4), key=lambda i: (heights[i], i))
    row = [0] * 7
    row[order[0]] = heights[order[1]] - heights[order[0]]
    row[order[3]] = heights[order[3]] - heights[order[2]]
    lower = frozenset(order[:2])
    side = lower if 0 in lower else frozenset(range(4)) - lower
    row[4 + QUAD_SIDES.index(side)] = heights[order[2]] - heights[order[1]]
    return tuple(row)


def _face_arcs(row, face):
    vertices = set(range(4)) - {face}
    arcs = {v: row[v] for v in vertices}
    for q, side in enumerate(QUAD_SIDES):
        cut = vertices & side
        singleton = cut if len(cut) == 1 else vertices - cut
        arcs[next(iter(singleton))] += row[4 + q]
    return arcs


@dataclass(frozen=True)
class SeedCertificate:
    """Primal potential and dual unit transshipment, with normal coordinates.

    Matching row (t, i, s, j) sends the unit from lower node t through the
    common global vertex vertices[t][i] == vertices[s][j] to upper node s.
    Sources and targets each occur once; its objective is h[s][j]-h[t][i].
    Statistics are measurements, not part of the mathematical certificate.
    """

    vertex_ids: tuple[int, ...]
    potential: tuple[int, ...]
    matching: tuple[tuple[int, int, int, int], ...]
    normal_coordinates: tuple[tuple[int, ...], ...]
    initial_disc_count: int
    disc_count: int
    statistics: dict

    def as_dict(self):
        return {
            'schema': 'fastunknot.cocycle-disc-seed.v1',
            'vertex_ids': list(self.vertex_ids),
            'potential': list(self.potential),
            'matching': [list(row) for row in self.matching],
            'normal_coordinates': [list(row) for row in self.normal_coordinates],
            'initial_disc_count': self.initial_disc_count,
            'disc_count': self.disc_count,
            'statistics': dict(self.statistics),
            'scope': 'minimum disc count among vertex-potential changes of input cocycle',
        }


def check_seed_certificate(vertices, heights, certificate):
    """Check a certificate without running the optimizer; raise on any defect.

    The proof checked is weak duality: for every matched pair through v,
    max(h_s+f)-min(h_t+f) >= h_sj-h_ti. Summing a permutation of sources and
    targets gives D(f) >= dual. Equality certifies global integer AND real
    optimality, independently of the network implementation.
    """
    vertices, heights, labels = _input(vertices, heights)
    if isinstance(certificate, SeedCertificate):
        data = certificate.as_dict()
    elif isinstance(certificate, dict):
        data = certificate
    else:
        raise ValueError('certificate must be a SeedCertificate or JSON object')
    if data.get('schema') != 'fastunknot.cocycle-disc-seed.v1':
        raise ValueError('unsupported certificate schema')
    if data.get('vertex_ids') != list(labels):
        raise ValueError('certificate vertex labels do not match the input')
    potential = data.get('potential')
    if (not isinstance(potential, (tuple, list)) or len(potential) != len(labels)
            or any(type(value) is not int for value in potential)):
        raise ValueError('one integral potential per global vertex is required')
    f = dict(zip(labels, potential))
    adjusted = tuple(tuple(h + f[v] for v, h in zip(vs, hs))
                     for vs, hs in zip(vertices, heights))
    coordinates = tuple(local_normal_coordinates(row) for row in adjusted)
    supplied = data.get('normal_coordinates')
    if (not isinstance(supplied, (list, tuple)) or len(supplied) != len(heights)
            or any(not isinstance(row, (list, tuple)) or len(row) != 7
                   or any(type(value) is not int or value < 0 for value in row)
                   for row in supplied)
            or tuple(tuple(row) for row in supplied) != coordinates):
        raise ValueError('normal coordinates do not equal the three local gaps')
    initial = sum(max(row) - min(row) for row in heights)
    primal = sum(sum(row) for row in coordinates)
    if type(data.get('initial_disc_count')) is not int or data['initial_disc_count'] != initial:
        raise ValueError('incorrect initial disc count')
    if type(data.get('disc_count')) is not int or data['disc_count'] != primal:
        raise ValueError('incorrect optimized disc count')
    matching = data.get('matching')
    if not isinstance(matching, (list, tuple)) or len(matching) != len(heights):
        raise ValueError('the dual matching needs one row per tetrahedron')
    sources, targets, dual = set(), set(), 0
    for row in matching:
        if (not isinstance(row, (list, tuple)) or len(row) != 4
                or any(type(value) is not int for value in row)):
            raise ValueError('a dual row must be four integers')
        t, i, s, j = row
        if not (0 <= t < len(heights) and 0 <= s < len(heights)
                and 0 <= i < 4 and 0 <= j < 4):
            raise ValueError('dual row index is out of range')
        if t in sources or s in targets:
            raise ValueError('dual matching repeats a source or target')
        if vertices[t][i] != vertices[s][j]:
            raise ValueError('dual row does not use a shared global vertex')
        sources.add(t)
        targets.add(s)
        dual += heights[s][j] - heights[t][i]
    if primal != dual:
        raise ValueError('primal and dual objectives differ')
    return {'primal': primal, 'dual': dual, 'verified': True}


def verify_seed_certificate(vertices, heights, certificate):
    """Boolean wrapper for use at an untrusted certificate boundary."""
    try:
        check_seed_certificate(vertices, heights, certificate)
    except (ValueError, TypeError, KeyError, IndexError):
        return False
    return True


@dataclass
class _Arc:
    to: int
    reverse: int
    capacity: int
    cost: int


def minimize_disc_seed(vertices, heights, check: Callable[[], None] | None = None):
    """Exact minimum of sum_t span(h[t] + f[vertices[t]]) with a certificate.

    Complexity is O(t*N*E) integer relaxations for t augmentations in this
    deliberately simple Bellman-Ford implementation. Since N,E=O(t), this is
    O(t^3), plus O(N*E) for potential extraction. Integer bit lengths are
    O(B + log(t)), where B bounds input height bit lengths. No numeric height
    is used as a capacity or as a loop bound. `check` may raise to cancel.
    """
    vertices, heights, labels = _input(vertices, heights)
    n, label_index = len(heights), {v: i for i, v in enumerate(labels)}
    original_nodes = 2 * n + len(labels)
    source, sink = original_nodes, original_nodes + 1
    graph = [[] for _ in range(original_nodes + 2)]
    references = []
    statistics = {'tetrahedra': n, 'vertices': len(labels), 'augmentations': 0,
                  'relaxations': 0, 'height_bits': max(abs(h).bit_length()
                                                     for row in heights for h in row)}

    def add(a, b, capacity, cost):
        index = len(graph[a])
        graph[a].append(_Arc(b, len(graph[b]), capacity, cost))
        graph[b].append(_Arc(a, index, 0, -cost))
        return a, index

    for t in range(n):
        add(source, t, 1, 0)
        add(n + t, sink, 1, 0)
        for i in range(4):
            v = 2 * n + label_index[vertices[t][i]]
            h = heights[t][i]
            # n+1 is strictly greater than the entire flow. These original
            # arcs remain residual-forward even after the last augmentation.
            references.append(('lower', t, i, add(t, v, n + 1, h)))
            references.append(('upper', t, i, add(v, n + t, n + 1, -h)))
    statistics['network_nodes'] = len(graph)
    statistics['network_arcs'] = sum(len(row) for row in graph) // 2

    for _ in range(n):
        if check:
            check()
        distances, previous = [None] * len(graph), [None] * len(graph)
        distances[source] = 0
        for _pass in range(len(graph) - 1):
            if check:
                check()
            changed = False
            for u, row in enumerate(graph):
                if distances[u] is None:
                    continue
                for i, arc in enumerate(row):
                    if not arc.capacity:
                        continue
                    candidate = distances[u] + arc.cost
                    statistics['relaxations'] += 1
                    if distances[arc.to] is None or candidate < distances[arc.to]:
                        distances[arc.to], previous[arc.to] = candidate, (u, i)
                        changed = True
            if not changed:
                break
        if distances[sink] is None:
            raise ArithmeticError('unit transshipment unexpectedly became infeasible')
        current, path = sink, []
        while current != source:
            if previous[current] is None or len(path) >= len(graph):
                raise ArithmeticError('invalid shortest augmenting path')
            u, i = previous[current]
            path.append((u, i))
            current = u
        for u, i in path:
            arc = graph[u][i]
            arc.capacity -= 1
            graph[arc.to][arc.reverse].capacity += 1
        statistics['augmentations'] += 1

    # The original transshipment's residual graph has no negative-cost cycle.
    # For each residual u->v with cost a, require x_v-x_u >= -a. Longest
    # distances from a zero-cost universal source give integral feasible x.
    constraints = []
    incoming, outgoing = defaultdict(list), defaultdict(list)
    for kind, t, i, (u, edge_index) in references:
        arc = graph[u][edge_index]
        flow = graph[arc.to][arc.reverse].capacity
        if flow not in (0, 1):
            raise ArithmeticError('a layered unit-flow arc is not integral and binary')
        constraints.append((u, arc.to, -arc.cost))
        if flow:
            constraints.append((arc.to, u, arc.cost))
            vertex = vertices[t][i]
            (incoming if kind == 'lower' else outgoing)[vertex].append((t, i))
    x = [0] * original_nodes
    for iteration in range(original_nodes):
        if check:
            check()
        changed = False
        for u, v, length in constraints:
            if x[v] < x[u] + length:
                x[v] = x[u] + length
                changed = True
        if not changed:
            break
        if iteration == original_nodes - 1:
            raise ArithmeticError('optimal flow has a positive residual cycle')
    f = [x[2 * n + i] for i in range(len(labels))]
    shift = min(f)
    f = tuple(value - shift for value in f)
    lookup = dict(zip(labels, f))
    coordinates = tuple(local_normal_coordinates(tuple(h + lookup[v]
                                                     for v, h in zip(vs, hs)))
                        for vs, hs in zip(vertices, heights))
    matching = []
    for vertex in labels:
        left, right = sorted(incoming[vertex]), sorted(outgoing[vertex])
        if len(left) != len(right):
            raise ArithmeticError('transshipment is not balanced at a global vertex')
        matching.extend((t, i, s, j) for (t, i), (s, j) in zip(left, right))
    certificate = SeedCertificate(
        labels, f, tuple(sorted(matching)), coordinates,
        sum(max(row) - min(row) for row in heights),
        sum(sum(row) for row in coordinates), statistics)
    check_seed_certificate(vertices, heights, certificate)
    return certificate


def face_pairing_data(gluings, local_heights):
    """Check reciprocal face pairings/cocycle compatibility and label vertices.

    `gluings[t][f]` is None, or (s,p), with p a permutation of 0..3. This
    adapter checks the gluing data and the additive local-height transitions;
    it does NOT establish that a supplied quotient is a compact 3-manifold.
    A validated finite triangulation is required for the geometric theorems.
    Ideal vertices must be truncated before applying those theorems.
    """
    heights = _rows(local_heights, 'heights')
    if not isinstance(gluings, (list, tuple)) or len(gluings) != len(heights):
        raise ValueError('one four-face gluing row per tetrahedron is required')
    n = len(heights)
    normalized = []
    for row in gluings:
        if not isinstance(row, (tuple, list)) or len(row) != 4:
            raise ValueError('each tetrahedron must specify four face gluings')
        converted = []
        for pairing in row:
            if pairing is None:
                converted.append(None)
                continue
            if not isinstance(pairing, (list, tuple)) or len(pairing) != 2:
                raise ValueError('a face pairing must be (tetrahedron, permutation)')
            s, p = pairing
            if (type(s) is not int or not 0 <= s < n
                    or not isinstance(p, (tuple, list)) or len(p) != 4
                    or any(type(i) is not int for i in p) or sorted(p) != list(range(4))):
                raise ValueError('invalid face pairing')
            converted.append((s, tuple(p)))
        normalized.append(tuple(converted))
    parents = list(range(4 * n))

    def root(a):
        while parents[a] != a:
            parents[a] = parents[parents[a]]
            a = parents[a]
        return a

    for t, row in enumerate(normalized):
        for face, pairing in enumerate(row):
            if pairing is None:
                continue
            s, p = pairing
            if (s, p[face]) == (t, face):
                raise ValueError('a face cannot be paired to itself')
            inverse = tuple(p.index(i) for i in range(4))
            if normalized[s][p[face]] != (t, inverse):
                raise ValueError('face pairings must be reciprocal')
            differences = {heights[s][p[i]] - heights[t][i]
                           for i in range(4) if i != face}
            if len(differences) != 1:
                raise ValueError('local heights do not define a compatible integral cocycle')
            for i in range(4):
                if i != face:
                    a, b = root(4 * t + i), root(4 * s + p[i])
                    parents[max(a, b)] = min(a, b)
    vertices = tuple(tuple(root(4 * t + i) for i in range(4)) for t in range(n))
    return tuple(normalized), vertices, heights


def check_glued_normal_coordinates(gluings, coordinates):
    """Check nonnegative admissibility and every paired-face matching equation."""
    if len(gluings) != len(coordinates):
        raise ValueError('normal-coordinate row count differs from tetrahedron count')
    for row in coordinates:
        if (len(row) != 7 or any(type(value) is not int or value < 0 for value in row)
                or sum(value != 0 for value in row[4:]) > 1):
            raise ValueError('invalid normal-coordinate row')
    for t, row in enumerate(gluings):
        for face, pairing in enumerate(row):
            if pairing is not None:
                s, p = pairing
                a, b = _face_arcs(coordinates[t], face), _face_arcs(coordinates[s], p[face])
                if any(a[i] != b[p[i]] for i in a):
                    raise ValueError('normal matching equation fails')
    return True


def optimize_face_pairing_cocycle(gluings, local_heights, check=None):
    """Optimize a glued cocycle after combinatorial compatibility checks."""
    gluings, vertices, heights = face_pairing_data(gluings, local_heights)
    result = minimize_disc_seed(vertices, heights, check)
    check_glued_normal_coordinates(gluings, result.normal_coordinates)
    return result


def optimize_triangulated_cocycle(triangulation, cocycle, check=None):
    """Adapter for a validated finite-triangulation object, including archive02.

    Required protocol: tetrahedra, vertex_classes, edge_endpoints, edge_value,
    and dual_surface. The object's dual_surface validates the cocycle and
    returns an object with .coordinates and .disc_count. This routine returns
    (certificate, optimized_surface). It does not import the object's module.
    """
    initial = triangulation.dual_surface(cocycle)
    n = triangulation.tetrahedra
    vertices = tuple(tuple(triangulation.vertex_classes[4 * t + i] for i in range(4))
                     for t in range(n))
    heights = tuple(tuple(triangulation.edge_value(cocycle, t, 0, i) for i in range(4))
                    for t in range(n))
    result = minimize_disc_seed(vertices, heights, check)
    potential = dict(zip(result.vertex_ids, result.potential))
    optimized = tuple(c + potential[b] - potential[a]
                      for c, (a, b) in zip(cocycle, triangulation.edge_endpoints))
    surface = triangulation.dual_surface(optimized)
    if (surface.coordinates != result.normal_coordinates
            or initial.disc_count != result.initial_disc_count):
        raise ArithmeticError('triangulation adapter disagrees with local normal coordinates')
    return result, surface
