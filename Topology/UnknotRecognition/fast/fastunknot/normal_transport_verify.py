"""Source-bound replay of transported coherent normal-disc witnesses.

The verifier imports no exterior constructor, cocycle solver, move producer,
descent planner, or interval-orbit search.  A positive count is required;
Euler characteristic alone never establishes the knot verdict.
"""

from .diagram import Diagram, DiagramError
from .diagram_exterior_verify import verify_diagram_exterior
from .boundary_shellings_verify import verify_boundary_shellings
from .cocycle_transport_verify import (
    verify_cocycle_transport, _read_heights, _check_signed_edges,
)
from .normal_surface_geometry import _prepare, _quad, NormalOrbitError
from .normal_disk_kernel import verify_normal_disk_count_certificate
from .integer_codec import certificate_equal, encoded_integer
from .cocycle_gauge_verify import verify_cocycle_gauge


class _CallbackRaised(BaseException):
    """Carry a caller exception through malformed-certificate handlers."""

    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def _callback_safe_call(function, check, *args, **kwargs):
    def guarded_check():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None

    try:
        return function(*args, check=guarded_check, **kwargs)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None


def verify_transport_disk_certificate(diagram, certificate, *, check=lambda: None):
    """Verify a compact exterior, optional shellings, moves, and terminal disc.

    The represented coherent fibre can change topology between moves.  The
    final component certificate is what proves an essential embedded disc.
    Malformed certificates return False; cooperative cancellation propagates.
    """
    return _callback_safe_call(_verify_transport_disk_certificate, check,
                               diagram, certificate)


def _verify_transport_disk_certificate(diagram, certificate, *, check):
    check()
    fields = {'schema', 'input_pd', 'source_triangulation', 'shelling',
              'source_heights', 'steps', 'coordinates', 'disc_certificate'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] not in ('diagram-transport-disc-v1','diagram-transport-disc-v2')
            or type(certificate['steps']) is not list):
        return False
    try:
        source = Diagram.from_pd(diagram.pd)
    except (DiagramError, AttributeError, TypeError):
        return False
    if not certificate_equal(certificate['input_pd'], [list(r) for r in source.pd]):
        return False
    raw = certificate['source_triangulation']
    if not verify_diagram_exterior(source, raw, check=check):
        return False
    shelling = certificate['shelling']
    if shelling is not None:
        if (type(shelling) is not dict or set(shelling) != {'triangulation', 'moves'}
                or not verify_boundary_shellings(raw, shelling['triangulation'],
                                                  shelling['moves'], check=check)):
            return False
        raw = shelling['triangulation']
    try:
        prepared = _prepare(raw, check)
        heights = _read_heights(certificate['source_heights'],
                                len(prepared['tetrahedra']), check)
        if heights is None or not _check_signed_edges(prepared, heights, check):
            return False
        for step in certificate['steps']:
            check()
            if type(step)is dict and set(step)=={'gauge'}:
                if (certificate['schema']!='diagram-transport-disc-v2'
                        or not verify_cocycle_gauge(raw,heights,step['gauge'],check=check)):return False
                heights=_read_heights(step['gauge']['heights'],len(raw['tetrahedra']),check)
                continue
            if type(step) is not dict or set(step) != {'triangulation', 'transport'}:
                return False
            if not verify_cocycle_transport(raw, heights, step['triangulation'],
                                           step['transport'], check=check):
                return False
            raw = step['triangulation']
            heights = _read_heights(step['transport']['heights'],
                                    len(raw['tetrahedra']), check)
        # Reconstruct coherent coordinates independently of local_coordinates.
        expected = []
        for row in heights:
            check()
            a, b, c, d = sorted(range(4), key=lambda v: (row[v], v))
            vector = [0]*7
            vector[a] = row[b]-row[a]
            vector[d] = row[d]-row[c]
            vector[4+_quad(a, b)] = row[c]-row[b]
            expected.append(vector)
        if not certificate_equal(certificate['coordinates'], expected):
            return False
        proof = certificate['disc_certificate']
        if not verify_normal_disk_count_certificate(raw, expected, proof, check=check):
            return False
        count = encoded_integer(proof['compressing_disk_components'])
    except (ValueError, KeyError, TypeError, IndexError, NormalOrbitError):
        return False
    check()
    return count > 0
