"""Independent replay of a source-bound geometric D or UDD first descent.

Each elementary move is checked as a formal relative-boundary replacement,
including identifications among the region's boundary facets. The elementary
checkers validate every source as a finite orientable torus-boundary manifold.
No move producer, search, cochain transport, or LP solver is imported.
"""
from hashlib import sha256
import json

from .pachner23_verify import verify_pachner_23
from .pachner32_verify import verify_pachner_32


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def verify_normal_geometric_descent(source, packet, *, check=lambda: None):
    """Verify preservation of the supplied manifold and a strict size decrease.

    Any source vertex count is supported. This does not certify a knot verdict.
    Malformed packets return False; exceptions from ``check`` retain identity,
    including exceptions that the nested geometry checkers ordinarily catch.
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
    except (ValueError, TypeError, KeyError, IndexError, AttributeError,
            OverflowError, RecursionError):
        return False


def _same(actual, expected, check):
    """Literal equality rejects bool/int and float/int substitutions."""
    check()
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return actual.keys() == expected.keys() and all(
            _same(actual[k], value, check) for k, value in expected.items())
    if type(expected) is list:
        return len(actual) == len(expected) and all(
            _same(a, b, check) for a, b in zip(actual, expected))
    return actual == expected


def _verify(source, packet, check):
    check()
    if (type(source) is not dict or set(source) != {'tetrahedra'} or
            type(source['tetrahedra']) is not list or
            type(packet) is not dict or
            set(packet) != {'schema', 'source_sha256', 'steps', 'successor'} or
            type(packet['schema']) is not str or
            packet['schema'] != 'normal-geometric-descent-v1' or
            type(packet['source_sha256']) is not str or
            type(packet['steps']) is not list or len(packet['steps']) not in (1, 3)):
        return False
    count = len(source['tetrahedra'])
    if count < 2:
        return False
    digest = sha256(json.dumps(source, sort_keys=True,
                               separators=(',', ':')).encode('utf-8')).hexdigest()
    check()
    if packet['source_sha256'] != digest:
        return False
    kinds = ('pachner-32-v1',) if len(packet['steps']) == 1 else (
        'pachner-23-v1', 'pachner-32-v1', 'pachner-32-v1')
    sizes = (count-1,) if len(kinds) == 1 else (count+1, count, count-1)
    current = source
    for step, kind, size in zip(packet['steps'], kinds, sizes):
        check()
        if (type(step) is not dict or set(step) != {'triangulation', 'certificate'} or
                type(step['triangulation']) is not dict or
                set(step['triangulation']) != {'tetrahedra'} or
                type(step['triangulation']['tetrahedra']) is not list or
                len(step['triangulation']['tetrahedra']) != size or size < 1 or
                type(step['certificate']) is not dict or
                type(step['certificate'].get('schema')) is not str or
                step['certificate']['schema'] != kind):
            return False
        verifier = verify_pachner_23 if kind == 'pachner-23-v1' else verify_pachner_32
        if not verifier(current, step['triangulation'], step['certificate'], check=check):
            return False
        current = step['triangulation']
    return _same(packet['successor'], current, check)
