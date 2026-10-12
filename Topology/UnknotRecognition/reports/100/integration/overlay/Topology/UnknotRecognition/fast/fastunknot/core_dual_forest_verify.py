"""Independent endpoint reconstruction and relative dual-forest replay.

The caller must first authenticate the full normal-parallelity geometry.
This module imports no forest, handlebody, or parallelity producer.  It
reconstructs the 2/3 incidences from all source edge flags, checks an arbitrary
supplied valid rooted cancellation order, and returns the reduced charts.
Malformed proof fields return None; source errors and cancellation callback
exceptions retain the enclosing source checker's exception behavior.
"""

from .integer_codec import certificate_equal, encoded_integer
from .normal_surface_geometry import _edge, _prepare, _quad


def replay_core_dual_forest(geometry, certificate, *, check=lambda: None):
    """Return reduced authenticated charts, or None for an invalid certificate."""
    check()
    fields = {'schema', 'source_sides', 'cancellations', 'surviving_two_handles'}
    if type(certificate) is not dict or set(certificate) != fields:
        return None
    if certificate['schema'] != 'normal-core-dual-forest-v1':
        return None
    if type(certificate['cancellations']) is not list:
        return None
    source = _prepare(geometry['source'], check)
    core = geometry['core']
    rows = geometry['coordinates']
    border = set()
    for t, f in source['boundary_faces']:
        check()
        border.update(source['vertex_roots'][4 * t + v]
                      for v in range(4) if v != f)
    flags_by_root = {}
    for i, root in enumerate(source['vertex_roots']):
        check()
        if root not in border:
            flags_by_root.setdefault(root, []).append([i // 4, i % 4])
    interior = sorted(flags_by_root)
    if len(interior) != len(core['handles3']):
        return None
    by_vertex = {}
    for number, root in enumerate(interior):
        check()
        flags = flags_by_root[root]
        expected = dict(id=number, vertex=root, link_triangles=flags)
        if not certificate_equal(core['handles3'][number], expected):
            return None
        by_vertex[root] = number

    incidences = []
    for number, disc in enumerate(core['handles2']):
        check()
        if type(disc['id']) is not int or disc['id'] != number:
            return None
        path = disc['cycle']
        if type(path) is not list or not path or len(path) % 2:
            return None
        common = None
        for flag in path[::2]:
            check()
            if flag['dimension'] != 0:
                return None
            t = flag['tetrahedron']
            a, b = flag['local_edge']
            if not (0 <= t < len(rows) and 0 <= a < b < 4):
                return None
            local = _edge(t, a, b)
            if source['edge_roots'][local] != disc['edge']:
                return None
            weight = rows[t][a] + rows[t][b] + sum(rows[t][4:])
            weight -= rows[t][4 + _quad(a, b)]
            ends = [by_vertex.get(source['vertex_roots'][4 * t + v], -1)
                    for v in (a, b)]
            if source['edge_orientations'][local]:
                ends.reverse()
            rank = disc['rank']
            if weight == 0:
                if rank != 0:
                    return None
                side = ends
            elif weight > 0 and rank == 0:
                side = [ends[0], -1]
            elif weight > 0 and rank == weight:
                side = [-1, ends[1]]
            else:
                return None
            if common is not None and common != side:
                return None
            common = side
        incidences.append(common)
    if not certificate_equal(certificate['source_sides'], incidences):
        return None

    live = set(range(len(interior)))
    used = set()
    for move in certificate['cancellations']:
        check()
        if type(move) is not list or len(move) != 2:
            return None
        try:
            vertex, edge = map(encoded_integer, move)
        except ValueError:
            return None
        if vertex not in live or edge in used or not 0 <= edge < len(incidences):
            return None
        a, b = incidences[edge]
        # A loop has two incidences and can never be a singleton pivot.
        if (a == vertex) + (b == vertex) != 1:
            return None
        other = b if a == vertex else a
        if other != -1 and other in live:
            return None
        live.remove(vertex)
        used.add(edge)
    if live:
        return None
    survivor_ids = [i for i in range(len(incidences)) if i not in used]
    if not certificate_equal(certificate['surviving_two_handles'], survivor_ids):
        return None
    reduced_discs = []
    for new_id, old_id in enumerate(survivor_ids):
        check()
        reduced_discs.append(dict(core['handles2'][old_id], id=new_id))
    check()
    return dict(core, handles2=reduced_discs, handles3=[])
