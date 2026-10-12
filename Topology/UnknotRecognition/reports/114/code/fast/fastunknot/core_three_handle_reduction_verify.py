"""Independent replay of the source core's dual two/three cancellation forest.

Endpoint owners come from authenticated vertex-link triangles. Edge weights
are computed directly in the canonical root tetrahedron. No producer, source
preparer, normal-coordinate analyser, or reduction planner is imported.
"""
from itertools import combinations
from .integer_codec import certificate_equal, encoded_integer


def replay_core_three_handles(geometry, certificate, *, check=lambda: None):
    """Return reduced geometry after exact source endpoint and move replay."""
    check()
    fields = {'schema', 'dual_endpoints', 'cancellations', 'surviving_two_handles'}
    if type(certificate) is not dict or set(certificate) != fields:
        return None
    if certificate['schema'] != 'core-three-handle-reduction-v1':
        return None
    core = geometry['core']
    vertex_owner = {}
    for h in core['handles3']:
        check()
        for triangle in h['link_triangles']:
            key = tuple(triangle)
            if key in vertex_owner:
                return None
            vertex_owner[key] = h['id']
    local_edges = list(combinations(range(4), 2))
    ends, expected = [], []
    for h in core['handles2']:
        check()
        t, edge = divmod(h['edge'], 6)
        a, b = local_edges[edge]
        row = geometry['coordinates'][t]
        # A quad misses precisely the two edges in its defining partition.
        missing = next(q for q in range(3) if {a,b} in (
            {0,q+1}, set(range(4))-{0,q+1}))
        weight = row[a]+row[b]+sum(row[4:])-row[4+missing]
        if h['rank'] not in (0,weight):
            return None
        pair = [vertex_owner.get((t,a)), vertex_owner.get((t,b))]
        if weight > 0:
            pair = [pair[0],None] if h['rank']==0 else [None,pair[1]]
        ends.append(pair)
        expected.append(dict(two_handle=h['id'], ends=pair))
    if not certificate_equal(certificate['dual_endpoints'], expected):
        return None
    moves = certificate['cancellations']
    if type(moves) is not list or len(moves) != len(core['handles3']):
        return None
    live_three = {h['id'] for h in core['handles3']}
    live_two = set(range(len(ends)))
    for move in moves:
        check()
        if type(move) is not dict or set(move) != {'two_handle','three_handle'}:
            return None
        try:
            e, v = encoded_integer(move['two_handle']), encoded_integer(move['three_handle'])
        except ValueError:
            return None
        if e not in live_two or v not in live_three:
            return None
        active = [end for end in ends[e] if end in live_three]
        # Repeated endpoints are two intersections, not a single owner.
        if active != [v]:
            return None
        live_two.remove(e)
        live_three.remove(v)
    if live_three:
        return None
    kept = sorted(live_two)
    if not certificate_equal(certificate['surviving_two_handles'], kept):
        return None
    check()
    return dict(geometry, core=dict(core, handles3=[], handles2=[
        dict(core['handles2'][old], id=new) for new, old in enumerate(kept)]))
