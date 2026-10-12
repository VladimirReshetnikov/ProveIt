"""Independent source endpoint reconstruction and relative 2/3 move replay.

The enclosing verifier first authenticates the ORIGINAL source geometry and
marked boundary.  This replay never calls the endpoint producer or scheduler.
It derives oriented endpoints by checking every local source-edge occurrence.
"""

from .integer_codec import certificate_equal
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint, _EDGES


def replay_core_top_reduction(triangulation, coordinates, geometry, certificate,
                              *, check=lambda: None):
    """Return the reduced authenticated geometry, or None for a bad proof.

Source geometry errors and callback exceptions propagate, as in the enclosing
normal-cut verifier.  The source-parallelity verifier must already have checked
all surviving attaching charts and the complete marked interface.
"""
    check()
    fields = {'schema', 'input_sha256', 'moves', 'surviving_two_handles'}
    if (type(certificate) is not dict or set(certificate) != fields or
            certificate['schema'] != 'normal-core-top-reduction-v1'):
        return None
    moves, surviving = certificate['moves'], certificate['surviving_two_handles']
    if type(moves) is not list or type(surviving) is not list:
        return None
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return None
    if (not certificate_equal(geometry['source'], triangulation) or
            not certificate_equal(geometry['coordinates'], analysed['rows'])):
        return None
    boundary = set()
    for t, f in prepared['boundary_faces']:
        check()
        boundary.update(prepared['vertex_roots'][4*t+v] for v in range(4) if v != f)
    vertices = sorted(set(prepared['vertex_roots']) - boundary)
    core = geometry['core']
    if len(core['handles3']) != len(vertices):
        return None
    vertex_handle = {}
    for i, (vertex, handle) in enumerate(zip(vertices, core['handles3'])):
        check()
        if (type(handle['id']) is not int or handle['id'] != i or
                type(handle['vertex']) is not int or handle['vertex'] != vertex):
            return None
        vertex_handle[vertex] = i

    # Reconstruct a consistently oriented endpoint pair from ALL local edges,
    # independently of the producer's single canonical representative.
    endpoints = {}
    for t in range(len(prepared['tetrahedra'])):
        for j, (a, b) in enumerate(_EDGES):
            check()
            local = 6*t+j
            edge = prepared['edge_roots'][local]
            pair = [prepared['vertex_roots'][4*t+a], prepared['vertex_roots'][4*t+b]]
            if prepared['edge_orientations'][local]:
                pair.reverse()
            if edge in endpoints and endpoints[edge] != pair:
                return None
            endpoints[edge] = pair
    contacts = []
    for edge in sorted(endpoints):
        check()
        if edge in prepared['boundary_incidence']:
            continue
        weight = analysed['weights'][edge]
        ranks = (0,) if weight == 0 else (0, weight)
        for rank in ranks:
            i = len(contacts)
            if i >= len(core['handles2']):
                return None
            handle = core['handles2'][i]
            if (any(type(handle[k]) is not int for k in ('id', 'edge', 'rank')) or
                    (handle['id'], handle['edge'], handle['rank']) != (i, edge, rank)):
                return None
            pair = endpoints[edge]
            adjacent = pair if weight == 0 else [pair[0 if rank == 0 else 1]]
            contacts.append([vertex_handle[v] for v in adjacent if v in vertex_handle])
    if len(contacts) != len(core['handles2']) or len(moves) != len(vertices):
        return None
    alive = set(range(len(vertices)))
    unused = set(range(len(contacts)))
    for move in moves:
        check()
        if (type(move) is not list or len(move) != 2 or
                any(type(v) is not int for v in move)):
            return None
        edge, vertex = move
        if edge not in unused or vertex not in alive:
            return None
        # Multiplicity matters. In particular [vertex, vertex] cannot pass.
        if [v for v in contacts[edge] if v in alive] != [vertex]:
            return None
        unused.remove(edge)
        alive.remove(vertex)
    expected = [e for e in range(len(contacts)) if e in unused]
    if alive or any(type(i) is not int for i in surviving) or surviving != expected:
        return None
    reduced_core = dict(core, handles3=[], handles2=[
        dict(core['handles2'][old], id=i) for i, old in enumerate(surviving)])
    check()
    return dict(geometry, core=reduced_core)
