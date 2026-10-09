"""Independent Regina component-weight oracle and deterministic real fixtures."""

from collections import Counter
import random

from fastunknot.normal_surface_geometry import _prepare, _edge, _EDGES
from normal_orbit_research.fixtures import (
    layered_torus, boundary_cap, interior_vertex_torus,
    regina_triangulation, regina_surface, export_surface,
)


def regina_profiles(raw, coordinates, cycle_edges):
    """Read component cells and edge weights directly from Regina.

    The selected two cycles are shared input, but this oracle does not use
    the new cellular allocation, weighted replay, or interval scheduler.
    """
    prepared = _prepare(raw, lambda: None)
    native = regina_triangulation(raw)
    root_to_native = {}
    for t in range(len(raw['tetrahedra'])):
        for a, b in _EDGES:
            root = prepared['edge_roots'][_edge(t, a, b)]
            index = native.tetrahedron(t).edge(a, b).index()
            if root in root_to_native and root_to_native[root] != index:
                raise AssertionError('native edge identification differs')
            root_to_native[root] = index
    surface = regina_surface(native, coordinates)
    result = Counter()
    disks = compressing = components = 0
    for part in surface.components():
        weight = lambda edge: int(str(part.edgeWeight(root_to_native[edge])))
        vector = (
            int(str(part.eulerChar())),
            sum(map(sum, export_surface(part))),
            sum(weight(edge) for edge in prepared['boundary_incidence']),
            sum(weight(edge) for edge in cycle_edges[0]),
            sum(weight(edge) for edge in cycle_edges[1]),
        )
        result[vector] += 1
        components += 1
        disks += (part.isOrientable() and vector[0] == 1 and part.countBoundaries() == 1)
        compressing += part.isCompressingDisc()
    return result, dict(components=components, disk_components=disks,
                        compressing_disk_components=compressing)


def fixture_corpus(seed=26100941, max_tetrahedra=6, trials=24):
    """Small valid embedded surfaces, including sums and repeated boundary edges."""
    import regina
    rng = random.Random(seed)
    cases = []
    for count in range(1, max_tetrahedra + 1):
        raw, meridian = layered_torus(count)
        cases.append((f'meridian-{count}', raw, meridian))
        native = regina_triangulation(raw)
        vertices = [export_surface(s) for s in
                    regina.NormalSurfaces(native, regina.NS_STANDARD)]
        for i, vector in enumerate(vertices):
            cases.append((f'vertex-{count}-{i}', raw, vector))
        for i in range(trials):
            left, right = rng.choice(vertices), rng.choice(vertices)
            if any(sum(bool(a or b) for a, b in zip(x[4:], y[4:])) > 1
                   for x, y in zip(left, right)):
                continue
            a, b = rng.randrange(1, 5), rng.randrange(1, 5)
            vector = [[a*x+b*y for x, y in zip(l, r)] for l, r in zip(left, right)]
            cases.append((f'sum-{count}-{i}', raw, vector))
        if count in (1, 3, 5):
            for caps in range(1, 4):
                raw, meridian = boundary_cap(raw, meridian)
                cases.append((f'capped-meridian-{count}-{caps}', raw, meridian))
    raw, basis = interior_vertex_torus()
    values = list(basis.values())
    for a in range(4):
        for b in range(4):
            for c in range(4):
                coefficients = (a, b, c)
                vector = [[sum(coefficients[k]*values[k][t][j] for k in range(3))
                           for j in range(7)] for t in range(4)]
                cases.append((f'interior-mix-{a}-{b}-{c}', raw, vector))
    return cases
