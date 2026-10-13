"""Remove one independently checked boundary layer from a finite source.

The source must already describe a compact connected orientable manifold with
one torus boundary. Only one-vertex sources are considered: their two boundary
triangles determine at most one possible top tetrahedron. Deletion is accepted
only by the separate inverse-layer verifier. This operation preserves the
compact manifold; it supplies no knot verdict or peripheral-coordinate map.
"""
from hashlib import sha256
import json

from .normal_surface_geometry import _prepare
from .boundary_unlayer_verify import verify_boundary_unlayering


def unlayer_boundary_once(triangulation, *, check=lambda: None):
    """Return UNLAYERED with a proof, or UNCHANGED with no proof.

    Labels of surviving tetrahedra retain their order and local vertex labels.
    There is no normal-surface or LP search. Invalid source inputs raise the
    native source-validation error; caller callback exceptions propagate.
    """
    p = _prepare(triangulation, check)
    n = len(p['tetrahedra'])
    stats = dict(initial_tetrahedra=n, remaining_tetrahedra=n,
                 candidate_tests=0, moves=0)

    def unchanged(reason):
        check()
        return dict(status='UNCHANGED', reason=reason, stats=stats)

    if p['vertices'] != 1:
        return unchanged('source has more than one vertex')
    boundary = p['boundary_faces']
    if len(boundary) != 2:
        raise ArithmeticError('one-vertex torus boundary has other than two faces')
    if boundary[0][0] != boundary[1][0]:
        return unchanged('boundary triangles belong to different tetrahedra')
    top = boundary[0][0]
    if n == 1:
        return unchanged('cannot remove the only tetrahedron')
    attachments = [r for r in p['tetrahedra'][top] if r is not None]
    if len(attachments) != 2:
        raise ArithmeticError('candidate layer has other than two attached faces')
    if any(r['tetrahedron'] == top for r in attachments):
        return unchanged('candidate has a self-paired attached face')

    rows = []
    for t, row in enumerate(p['tetrahedra']):
        check()
        if t == top:
            continue
        rows.append([None if r is None or r['tetrahedron'] == top else
            dict(tetrahedron=r['tetrahedron']-int(r['tetrahedron'] > top),
                 permutation=list(r['permutation'])) for r in row])
    successor = dict(tetrahedra=rows)
    raw = json.dumps(triangulation, sort_keys=True, separators=(',', ':'))
    packet = dict(schema='normal-boundary-unlayer-v1',
        source_sha256=sha256(raw.encode('utf-8')).hexdigest(),
        tetrahedron=top, successor=successor)
    stats['candidate_tests'] += 1
    if not verify_boundary_unlayering(triangulation, packet, check=check):
        return unchanged('candidate deletion is not a certified inverse layer')
    stats.update(remaining_tetrahedra=n-1, moves=1)
    check()
    return dict(status='UNLAYERED', certificate=packet, stats=stats)
