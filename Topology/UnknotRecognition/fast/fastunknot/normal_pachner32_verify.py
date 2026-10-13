"""Independent source-bound replay of a strictly shrinking Pachner 3--2 move.

The legacy relative-boundary checker validates both finite orientable compact
torus-boundary manifolds and the complete formal bipyramid boundary map. This
includes identifications between boundary facets of the region itself; the
formal vertices need not be distinct global vertices. No producer, search
backend, or external topology engine is imported, and no knot verdict follows
from this source-only certificate.
"""

from hashlib import sha256
import json

from .pachner32_verify import verify_pachner_32


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def verify_normal_pachner32(source, packet, *, check=lambda: None):
    """Verify an exact ``normal-pachner-32-v1`` packet against its source.

    Malformed packets return False. Caller exceptions always propagate with
    their original identity, including those raised within legacy manifold
    validation. Neither source nor successor is restricted to one vertex.
    """
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None

    try:
        return _verify(source, packet, guarded)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False


def _verify(source, packet, check):
    check()
    if (type(packet) is not dict or
            set(packet) != {'schema', 'source_sha256', 'certificate', 'successor'} or
            type(packet['schema']) is not str or
            packet['schema'] != 'normal-pachner-32-v1' or
            type(packet['source_sha256']) is not str):
        return False
    successor = packet['successor']
    for triangulation in (source, successor):
        if (type(triangulation) is not dict or set(triangulation) != {'tetrahedra'} or
                type(triangulation['tetrahedra']) is not list):
            return False
    count = len(source['tetrahedra'])
    if count < 3 or len(successor['tetrahedra']) != count-1:
        return False
    certificate = packet['certificate']
    if (type(certificate) is not dict or
            type(certificate.get('schema')) is not str):
        return False
    digest = sha256(json.dumps(source, sort_keys=True,
                               separators=(',', ':')).encode('utf-8')).hexdigest()
    check()
    if packet['source_sha256'] != digest:
        return False
    # The guarded callback escapes the legacy malformed-input catch even when
    # the caller raises NormalOrbitError, preserving cancellation semantics.
    return verify_pachner_32(source, successor, certificate, check=check)
