"""Relative 2/3 cancellations in an authenticated compressed normal-cut core.

The source edge gaps retain both belt-disk ends, with multiplicity.  Boundary
ends are represented by None.  Growing a forest from these boundary ends
removes all source vertex three-handles.  The moves avoid every recorded
parallelity port; surviving attaching cycles are retained verbatim.

This module does not authenticate arbitrary handle presentations.  Its
geometry argument must come from the source-parallelity reconstruction.
"""

from collections import deque

from .integer_codec import certificate_equal
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint, _EDGES


def source_core_top_incidence(triangulation, coordinates, geometry, *, check=lambda: None):
    """Reconstruct the two belt endpoints of each source exceptional edge gap.

IDs are those of the original core, before any row deletion or renumbering.
A loop at an interior vertex has endpoints [v, v], not a singleton set.
"""
    check()
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    if (not certificate_equal(geometry['source'], triangulation) or
            not certificate_equal(geometry['coordinates'], analysed['rows'])):
        raise ArithmeticError('top reduction source does not match its geometry')
    core = geometry['core']
    boundary = {prepared['vertex_roots'][4*t+v]
                for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
    vertices = sorted(set(prepared['vertex_roots']) - boundary)
    if [(h['id'], h['vertex']) for h in core['handles3']] != list(enumerate(vertices)):
        raise ArithmeticError('top reduction has inconsistent source vertex handles')
    by_vertex = {v: i for i, v in enumerate(vertices)}
    records = []
    for edge in sorted(set(prepared['edge_roots']) - prepared['boundary_incidence'].keys()):
        check()
        t, j = divmod(edge, 6)
        a, b = _EDGES[j]
        # A union-find root is its own oriented representative.  The last
        # local occurrence stored in prepared['endpoints'] need not be.
        if prepared['edge_roots'][edge] != edge or prepared['edge_orientations'][edge]:
            raise ArithmeticError('invalid canonical source edge orientation')
        ends = [by_vertex.get(prepared['vertex_roots'][4*t+v]) for v in (a, b)]
        weight = analysed['weights'][edge]
        for rank in ([0] if weight == 0 else [0, weight]):
            if weight == 0:
                belt = ends.copy()
            elif rank == 0:
                belt = [ends[0], None]
            else:
                belt = [None, ends[1]]
            records.append(dict(id=len(records), edge=edge, rank=rank, ends=belt))
    if len(core['handles2']) != len(records):
        raise ArithmeticError('top reduction has inconsistent source edge-gap inventory')
    for expected, handle in zip(records, core['handles2']):
        check()
        if (any(type(handle[key]) is not int for key in ('id', 'edge', 'rank')) or
                any(handle[key] != expected[key] for key in ('id', 'edge', 'rank'))):
            raise ArithmeticError('top reduction has an unauthenticated edge-gap address')
    return dict(input_sha256=_fingerprint(triangulation, analysed, check),
                two_handles=records, three_handles=vertices)


def rooted_top_plan(incidence, *, check=lambda: None):
    """Return (moves, surviving source IDs, statistics) for source incidence.

    The input is the endpoint packet from source_core_top_incidence.  This
    extracted queue allows scheduling costs to be measured independently of
    the common source validator and source-coordinate reconstruction.
"""
    check()
    edges = incidence['two_handles']
    alive = set(range(len(incidence['three_handles'])))
    remaining = set(range(len(edges)))
    incident = [[] for _ in alive]
    for edge in edges:
        check()
        # Store an edge once per vertex; keep its two endpoints in the edge
        # record so that a loop is never mistaken for an eligible end.
        for v in set(edge['ends']) - {None}:
            incident[v].append(edge['id'])
    queue = deque(edge['id'] for edge in edges
                  if sum(v in alive for v in edge['ends']) == 1)
    moves, visits, pops = [], 0, 0
    while alive:
        check()
        if not queue:
            raise ArithmeticError('source-cut vertex handles cannot reach a boundary root')
        e = queue.popleft()
        pops += 1
        if e not in remaining:
            continue
        ends = [v for v in edges[e]['ends'] if v in alive]
        if len(ends) != 1:
            continue
        v = ends[0]
        moves.append([e, v])
        remaining.remove(e)
        alive.remove(v)
        for other in incident[v]:
            check()
            visits += 1
            if (other in remaining and
                    sum(w in alive for w in edges[other]['ends']) == 1):
                queue.append(other)
    check()
    return (moves, [e for e in range(len(edges)) if e in remaining],
            dict(cancelled_23=len(moves), incidence_visits=visits, queue_pops=pops))


def reduce_core_top_handles(triangulation, coordinates, geometry, *, check=lambda: None):
    """Return (reduced geometry, relative cancellation proof, queue statistics).

    The source validator requires a connected manifold with nonempty boundary.
    Every component of the zero-weight interior-vertex graph therefore meets an
    old boundary vertex or a positive-weight edge.  The queue cannot stall on an
    authenticated source core.  No normal multiplicity is expanded.
    """
    incidence = source_core_top_incidence(triangulation, coordinates, geometry, check=check)
    moves, original_ids, stats = rooted_top_plan(incidence, check=check)
    core = geometry['core']
    reduced_core = dict(core, handles3=[], handles2=[
        dict(core['handles2'][source_id], id=i) for i, source_id in enumerate(original_ids)])
    proof = dict(schema='normal-core-top-reduction-v1',
                 input_sha256=incidence['input_sha256'], moves=moves,
                 surviving_two_handles=original_ids)
    check()
    return dict(geometry, core=reduced_core), proof, stats
