"""Construct a positive ray before searching a multiple-vertex exterior.

Burton--Ozlen, arXiv:1211.1079v3, Lemma 6 (pp. 11--14), constructs the
normal frontier of an expanded edge neighbourhood. Its components are discs
and spheres, including a non-vertex-link disc. Removing vertex-link components
therefore leaves positive canonical coordinates. Existing support descent turns
these into a primitive full-source extreme ray accepted by the crushing API.

The source validator checks a finite connected compact orientable manifold
with one torus boundary. Completeness of the reduction and preservation of the
original exterior use the classical knot-exterior premise of the authenticated
chain. This supplied-source producer emits no knot verdict or homeomorphism
claim. It expands no large coordinate multiplicity and performs no sector or
LP search. Source checks and support extraction add polynomial work to the
O(t**2) combinatorial subcomplex expansion.
"""

from .normal_surface_geometry import _prepare, _coordinates, _EDGES, _edge, _quad
from .positive_ray import extract_positive_ray


def _expanded_edge_link(prepared, check):
    vertices, edges = prepared['vertex_roots'], prepared['edge_roots']
    boundary_vertices = {vertices[4*t+v] for t, f in prepared['boundary_faces']
                         for v in range(4) if v != f}
    if len(boundary_vertices) > 1:
        eligible = [e for e, (a, b) in prepared['endpoints'].items()
                    if a != b and e in prepared['boundary_incidence']]
    else:
        eligible = [e for e, (a, b) in prepared['endpoints'].items()
                    if a != b and ((a in boundary_vertices) != (b in boundary_vertices))]
    if not eligible:
        raise ArithmeticError('multiple-vertex source has no eligible linking edge')
    seed = min(eligible)
    local = next((t, a, b) for t in range(len(prepared['tetrahedra']))
                 for a, b in _EDGES if edges[_edge(t, a, b)] == seed)
    included_edges = {seed}
    included_vertices = set(prepared['endpoints'][seed])
    face_ids, face_edges = {}, {}
    for t, row in enumerate(prepared['tetrahedra']):
        check()
        for f, gluing in enumerate(row):
            index = 4*t+f
            if gluing is not None:
                index = min(index, 4*gluing['tetrahedron']+gluing['permutation'][f])
            face_ids[t, f] = index
            face_edges[index] = tuple(edges[_edge(t, a, b)]
                                     for a, b in _EDGES if f not in (a, b))

    included_faces, additions = set(), []
    ordered_faces = sorted(face_edges.items())
    changed, passes = True, 0
    while changed:
        check()
        changed = False
        passes += 1
        for f, incident in ordered_faces:
            check()
            # Count local occurrences, not distinct global edge classes: the
            # same edge can appear twice around a face and cause a bent arc.
            if f in included_faces or sum(e in included_edges for e in incident) < 2:
                continue
            included_faces.add(f)
            included_edges.update(incident)
            for e in incident:
                included_vertices.update(prepared['endpoints'][e])
            additions.append(f)
            changed = True
    # Adding a tetrahedron with all faces present adds no new lower cells, so
    # these final closure steps need not trigger another face scan.
    absorbed = {t for t in range(len(prepared['tetrahedra']))
                if all(face_ids[t, f] in included_faces for f in range(4))}
    rows = [[0]*7 for _ in prepared['tetrahedra']]
    patterns = dict(tetrahedron=0, face=0, edges0=0, edges1=0, edges2=0)
    for t, row in enumerate(rows):
        check()
        if t in absorbed:
            patterns['tetrahedron'] += 1
            continue
        fs = [f for f in range(4) if face_ids[t, f] in included_faces]
        if len(fs) > 1:
            raise ArithmeticError('edge expansion stopped before tetrahedron closure')
        accounted = set()
        if fs:
            f = fs[0]
            row[f] += 1
            accounted.update(v for v in range(4) if v != f)
            patterns['face'] += 1
        else:
            es = [(a, b) for a, b in _EDGES if edges[_edge(t, a, b)] in included_edges]
            if len(es) > 2 or (len(es) == 2 and set(es[0]) & set(es[1])):
                raise ArithmeticError('edge expansion stopped before face closure')
            for a, b in es:
                row[4+_quad(a, b)] += 1
                accounted.update((a, b))
            patterns['edges'+str(len(es))] += 1
        # An additional E-vertex opposite an included face contributes a
        # second parallel triangle. Opposite included edges similarly give
        # two copies of the same quad type above.
        for v in range(4):
            if vertices[4*t+v] in included_vertices and v not in accounted:
                row[v] += 1
    return rows, dict(seed_edge=seed, seed_edge_local=list(local),
        seed_endpoints=list(prepared['endpoints'][seed]),
        boundary_vertices=len(boundary_vertices), face_additions=additions,
        absorbed_tetrahedra=sorted(absorbed), patterns=patterns, closure_passes=passes)


def vertex_reduction_ray(triangulation, *, check=lambda: None):
    """Return ONE_VERTEX or an independently crushable POSITIVE_EULER ray.

    ONE_VERTEX only reports the supplied triangulation's vertex count; it is
    not a recognition result. A positive result includes raw and canonically
    peeled link coordinates for diagnostics, and ``coordinates`` contains the
    primitive extracted ray. The caller must independently verify its crushing
    quotient and preserve diagram provenance. No local search cap is needed;
    callbacks are polled throughout and their exceptions propagate unchanged.
    """
    prepared = _prepare(triangulation, check)
    stats = dict(vertex_count=prepared['vertices'], tetrahedra=len(prepared['tetrahedra']),
                 face_additions=0, absorbed_tetrahedra=0, closure_passes=0,
                 raw_normal_pieces=0, raw_euler=0, canonical_euler=0,
                 maximum_raw_coordinate=0, peeled_vertex_links=0, descent_steps=0)
    if prepared['vertices'] == 1:
        check()
        return dict(status='ONE_VERTEX', coordinates=None, raw_coordinates=None,
                    canonical_coordinates=None, diagnostics=None, extraction_stats=None,
                    stats=stats)

    rows, diagnostics = _expanded_edge_link(prepared, check)
    raw = _coordinates(prepared, rows, check)
    minima = {}
    for corner, vertex in enumerate(prepared['vertex_roots']):
        check()
        value = rows[corner//4][corner % 4]
        minima[vertex] = min(minima.get(vertex, value), value)
    canonical = [row[:] for row in rows]
    for corner, vertex in enumerate(prepared['vertex_roots']):
        check()
        canonical[corner//4][corner % 4] -= minima[vertex]
    peeled = _coordinates(prepared, canonical, check)
    if peeled['euler_characteristic'] <= 0 or not any(any(row[4:]) for row in canonical):
        raise ArithmeticError('expanded-edge link has no canonical positive nonlink part')
    maximum = max(x for row in rows for x in row)
    if maximum > 2 or raw['normal_disks'] > 4*len(rows):
        raise ArithmeticError('expanded-edge link exceeded its local piece bound')
    result = extract_positive_ray(triangulation, canonical, check=check)
    diagnostics['peeled_vertex_links'] = [[v, m] for v, m in sorted(minima.items()) if m]
    stats.update(face_additions=len(diagnostics['face_additions']),
                 absorbed_tetrahedra=len(diagnostics['absorbed_tetrahedra']),
                 closure_passes=diagnostics['closure_passes'],
                 raw_normal_pieces=raw['normal_disks'], raw_euler=raw['euler_characteristic'],
                 canonical_euler=peeled['euler_characteristic'], maximum_raw_coordinate=maximum,
                 peeled_vertex_links=sum(minima.values()),
                 descent_steps=result['stats']['descent_steps'])
    check()
    return dict(status='POSITIVE_EULER', coordinates=result['coordinates'],
                raw_coordinates=rows, canonical_coordinates=canonical,
                diagnostics=diagnostics, extraction_stats=result['stats'], stats=stats)
