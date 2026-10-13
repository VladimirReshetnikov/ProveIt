"""Find one independently certified strict Pachner 3--2 reduction.

Inputs are finite connected orientable compact manifolds with one torus
boundary, with any number of vertices. A complete deterministic edge scan
finds a relative-boundary move; it supplies neither a knot verdict nor a
minimum-triangulation certificate. No normal-surface search runs here.
"""

from hashlib import sha256
import json

from .normal_surface_geometry import _EDGES, _prepare, NormalOrbitError
from .pachner32 import pachner_32
from .normal_pachner32_verify import verify_normal_pachner32


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def reduce_pachner32_once(triangulation, *, check=lambda: None):
    """Return REDUCED with a source-bound proof, or UNCHANGED after a full scan.

    Candidates are interior edges with exactly three local incidences in
    three distinct tetrahedra, ordered by their smallest local (tet, a, b)
    representative. Each accepted successor passes independent formal-boundary
    replay and finite manifold validation. A completed UNCHANGED result only
    excludes this strict class of moves. There is no work cap on the polynomial
    scan. Invalid sources raise the native validation error, and exceptions
    from the caller's callback always propagate with their original identity.
    """
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None

    try:
        return _reduce(triangulation, guarded)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None


def _reduce(triangulation, check):
    prepared = _prepare(triangulation, check)
    n = len(prepared['tetrahedra'])
    stats = dict(initial_tetrahedra=n, remaining_tetrahedra=n,
                 candidate_tests=0, moves=0, scan_complete=False)
    occurrences = {}
    for local, root in enumerate(prepared['edge_roots']):
        check()
        t, edge = divmod(local, 6)
        a, b = _EDGES[edge]
        occurrences.setdefault(root, []).append((t, a, b))
    candidates = []
    for root, incidences in occurrences.items():
        check()
        if (root not in prepared['boundary_incidence'] and
                len(incidences) == 3 and len({t for t, _, _ in incidences}) == 3):
            candidates.append(min(incidences))
    candidates.sort()
    digest = None
    for t, a, b in candidates:
        check()
        stats['candidate_tests'] += 1
        try:
            result = pachner_32(triangulation, t, [a, b], check=check)
        except NormalOrbitError:
            # Degree and distinctness are filters, not a formal-ball proof.
            # Callback failures escape this catch through the private carrier.
            continue
        if digest is None:
            digest = sha256(json.dumps(triangulation, sort_keys=True,
                separators=(',', ':')).encode('utf-8')).hexdigest()
        packet = dict(schema='normal-pachner-32-v1', source_sha256=digest,
                      certificate=result['certificate'],
                      successor=result['triangulation'])
        if not verify_normal_pachner32(triangulation, packet, check=check):
            continue
        stats.update(remaining_tetrahedra=n-1, moves=1)
        check()
        return dict(status='REDUCED', certificate=packet, stats=stats)
    stats['scan_complete'] = True
    check()
    reason = ('no eligible interior edge' if not candidates else
              'no candidate passed independent relative-boundary replay')
    return dict(status='UNCHANGED', reason=reason, stats=stats)
