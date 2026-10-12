"""Source-authenticated removal of core three-handles by a dual boundary forest.

The enclosing parallelity proof authenticates all source handles. A two-handle
may cancel a three-handle precisely when one of its two dual endpoints is that
remaining three-handle and its other endpoint is already on the boundary.
"""
from collections import deque

from .normal_surface_geometry import _prepare, _coordinates, _EDGES


def reduce_core_three_handles(geometry, *, check=lambda: None):
    """Return (reduced_geometry, certificate), or None if the forest stalls."""
    check()
    core = geometry['core']
    source = _prepare(geometry['source'], check)
    normal = _coordinates(source, geometry['coordinates'], check)
    by_vertex = {h['vertex']: h['id'] for h in core['handles3']}
    ends, records = {}, []
    for h in core['handles2']:
        check()
        t, edge = divmod(h['edge'], 6)
        a, b = _EDGES[edge]
        endpoints = [by_vertex.get(source['vertex_roots'][4*t+v]) for v in (a,b)]
        weight = normal['weights'][h['edge']]
        if weight:
            if h['rank'] == 0:
                endpoints[1] = None
            elif h['rank'] == weight:
                endpoints[0] = None
            else:
                raise ArithmeticError('non-extreme core edge gap')
        elif h['rank'] != 0:
            raise ArithmeticError('invalid zero-weight edge gap')
        ends[h['id']] = endpoints
        records.append(dict(two_handle=h['id'], ends=endpoints))
    # Each endpoint occurrence is indexed, including both ends of a loop.
    incident = {v: [] for v in by_vertex.values()}
    degree, owner = {}, {}
    for e, pair in ends.items():
        check()
        degree[e], owner[e] = 0, 0
        for v in pair:
            if v is not None:
                incident[v].append(e)
                degree[e] += 1
                owner[e] ^= v
    queue = deque(e for e in ends if degree[e] == 1)
    alive, remaining = set(incident), set(ends)
    moves = []
    while queue:
        check()
        e = queue.popleft()
        if e not in remaining or degree[e] != 1:
            continue
        v = owner[e]
        moves.append(dict(two_handle=e, three_handle=v))
        remaining.remove(e)
        alive.remove(v)
        for other in incident[v]:
            check()
            if other not in remaining:
                continue
            degree[other] -= 1
            owner[other] ^= v
            if degree[other] == 1:
                queue.append(other)
    if alive:
        return None
    kept = [h['id'] for h in core['handles2'] if h['id'] in remaining]
    reduced = dict(geometry, core=dict(core, handles3=[], handles2=[
        dict(core['handles2'][old], id=new) for new, old in enumerate(kept)]))
    proof = dict(schema='core-three-handle-reduction-v1', dual_endpoints=records,
                 cancellations=moves, surviving_two_handles=kept)
    check()
    return reduced, proof
