"""Independent full-cell verification of an aggregate peeled Pachner score.

The consumer imports neither the dynamic tree nor its scoring producer.
It recomputes vertex links and all cell counts on both finite manifolds.
"""
from .cocycle_transport_verify import _shield_callback, _read_heights, _check_signed_edges
from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates, _quad, NormalOrbitError
from .pachner_batch_verify import verify_pachner_32_batch


_FIELDS = {'raw_euler_gain', 'raw_piece_saving', 'link_euler_delta',
           'link_piece_delta', 'peeled_euler_gain', 'peeled_piece_saving'}


def _summary(triangulation, heights, check):
    prepared = _prepare(triangulation, check)
    heights = _read_heights(heights, len(prepared['tetrahedra']), check)
    if heights is None or not _check_signed_edges(prepared, heights, check):
        raise ValueError('invalid coherent heights')
    # Reconstruct each integer level interval directly, not via the producer.
    coordinates = []
    for h in heights:
        check()
        ordered = sorted(range(4), key=lambda v: (h[v], v))
        a, b, c, d = ordered
        row = [0]*7
        row[a] = h[b]-h[a]
        row[d] = h[d]-h[c]
        row[4+_quad(a, b)] = h[c]-h[b]
        coordinates.append(row)
    cell = _coordinates(prepared, coordinates, check)
    boundary = {prepared['vertex_roots'][4*t+v]
                for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
    values = {}
    for t, row in enumerate(coordinates):
        check()
        for v in range(4):
            values.setdefault(prepared['vertex_roots'][4*t+v], []).append(row[v])
    link_euler = sum((1 if v in boundary else 2)*min(rows) for v, rows in values.items())
    link_pieces = sum(len(rows)*min(rows) for rows in values.values())
    return dict(euler=cell['euler_characteristic'], pieces=cell['normal_disks'],
                link_euler=link_euler, link_pieces=link_pieces)


@_shield_callback
def verify_peeled_batch_score(before, heights, after, move_certificate,
                              score_certificate, *, check=lambda: None):
    check()
    if (type(score_certificate) is not dict
            or set(score_certificate) != _FIELDS | {'schema'}
            or score_certificate['schema'] != 'pachner-peeled-score-v1'):
        return False
    if not verify_pachner_32_batch(before, after, move_certificate,
                                  heights=heights, check=check):
        return False
    try:
        claimed = {k: encoded_integer(score_certificate[k]) for k in _FIELDS}
        old = _summary(before, heights, check)
        new = _summary(after, move_certificate['cocycle']['heights'], check)
    except (KeyError, ValueError, TypeError, NormalOrbitError):
        return False
    raw_euler = new['euler']-old['euler']
    raw_saving = old['pieces']-new['pieces']
    link_euler = new['link_euler']-old['link_euler']
    link_pieces = new['link_pieces']-old['link_pieces']
    expected = dict(raw_euler_gain=raw_euler, raw_piece_saving=raw_saving,
        link_euler_delta=link_euler, link_piece_delta=link_pieces,
        peeled_euler_gain=raw_euler-link_euler,
        peeled_piece_saving=raw_saving+link_pieces)
    check()
    return claimed == expected
