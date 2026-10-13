"""Independent Regina quotient, source-support rank and boundary observations."""
from math import gcd
import regina
from .fixtures import regina_triangulation, face_pairing


def component_census(triangulation):
    components = triangulation.triangulateComponents()
    return [dict(tetrahedra=sorted(t.index() for t in triangulation.component(i).tetrahedra()),
                 boundary_euler=sorted(int(b.eulerChar()) for b in component.boundaryComponents()))
            for i, component in enumerate(components)]


def support_rank(triangulation, coordinates):
    flat = [x for row in coordinates for x in row]
    support = [i for i, x in enumerate(flat) if x]
    equations = regina.makeMatchingEquations(triangulation, regina.NormalCoords.Standard)
    restricted = regina.MatrixInt(equations.rows(), len(support))
    for i in range(equations.rows()):
        for j, column in enumerate(support):
            restricted.set(i, j, equations.entry(i, column))
    return len(support), restricted.rank(), gcd(*flat)


def isolated_quad_cycles(source, rows):
    """Undirected face-state cycles erased without touching a retained endpoint."""
    tetrahedra = source['tetrahedra']
    quads = {i: next((q for q in range(3) if row[4+q]), None) for i, row in enumerate(rows)}
    quads = {i: q for i, q in quads.items() if q is not None}
    adjacency, endpoints = {}, set()
    for t, q in quads.items():
        pairs = [(0, q+1), tuple(v for v in range(4) if v not in (0, q+1))]
        for a, b in pairs:
            adjacency.setdefault((t, a), []).append((t, b))
            adjacency.setdefault((t, b), []).append((t, a))
        for f, face in enumerate(tetrahedra[t]):
            if face is not None and face['tetrahedron'] in quads:
                adjacency[t, f].append((face['tetrahedron'], face['permutation'][f]))
            else:
                endpoints.add((t, f))
    unseen, cycles = set(adjacency), []
    while unseen:
        first = min(unseen); unseen.remove(first); component = [first]
        for state in component:
            for other in adjacency[state]:
                if other in unseen:
                    unseen.remove(other); component.append(other)
        if not endpoints.intersection(component):
            cycles.append([list(state) for state in sorted(component)])
    return cycles


def inspect(source, rows):
    tri = regina_triangulation(source)
    surface = regina.NormalSurface(tri, regina.NormalCoords.Standard,
                                  [x for row in rows for x in row])
    support, rank, divisor = support_rank(tri, rows)
    quotient = surface.crush()
    assert quotient.isValid() and quotient.isOrientable()
    census = component_census(quotient)
    torus = [i for i, c in enumerate(census) if c['boundary_euler'] == [0]]
    assert len(torus) <= 1
    successor = (face_pairing(quotient.triangulateComponents()[torus[0]]) if torus else None)
    result = dict(euler=int(str(surface.eulerChar())), connected=surface.isConnected(),
        vertex_link=surface.isVertexLinking(), compressing_disc=surface.isCompressingDisc(),
        support=support, support_rank=rank, support_nullity=support-rank, divisor=divisor,
        quotient=face_pairing(quotient), components=census,
        torus_component=torus[0] if torus else None, successor=successor,
        isolated_cycles=isolated_quad_cycles(source, rows))
    result['eligible'] = (result['euler'] > 0 and not result['vertex_link'] and
                          support-rank == 1 and divisor == 1 and any(any(row[4:]) for row in rows))
    return result
