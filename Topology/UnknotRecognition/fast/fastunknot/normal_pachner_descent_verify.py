"""Independent source-bound replay of a zero-height, one-upward first descent.

The legacy endpoint inspector replays each formal relative-boundary Pachner
replacement and its exact cochain transport. The additional fixed policy here
requires the first strict decrease, at most three elementary moves, and an
exactly one-tetrahedron smaller endpoint. No discovery producer is imported.
"""
from hashlib import sha256
import json

from .pachner_cover_verify import inspect_pachner_descent


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def verify_normal_pachner_descent(source, packet, *, check=lambda: None):
    """Verify a fixed U=1 geometric macro on a finite torus-boundary source.

    Both one-vertex and multiple-vertex sources are supported. This proves
    preservation of the supplied compact manifold, not a standalone knot
    verdict. Malformed packets return False; caller exceptions retain identity.
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


def _zeros(rows, count, width, check):
    if type(rows) is not list or len(rows) != count:
        return False
    for row in rows:
        check()
        if (type(row) is not list or len(row) != width or
                any(type(value) is not int or value != 0 for value in row)):
            return False
    return True


def _same(actual, expected, check):
    """Literal equality also rejects bool/int and float/int substitutions."""
    check()
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return actual.keys() == expected.keys() and all(_same(actual[k], v, check) for k, v in expected.items())
    if type(expected) is list:
        return len(actual) == len(expected) and all(_same(a, b, check) for a, b in zip(actual, expected))
    return actual == expected


def _verify(source, packet, check):
    check()
    if (type(packet) is not dict or
            set(packet) != {'schema', 'source_sha256', 'certificate', 'successor'} or
            type(packet['schema']) is not str or packet['schema'] != 'normal-pachner-descent-v1' or
            type(packet['source_sha256']) is not str or type(source) is not dict or
            set(source) != {'tetrahedra'} or type(source['tetrahedra']) is not list):
        return False
    n = len(source['tetrahedra'])
    if n < 2:
        return False
    digest = sha256(json.dumps(source, sort_keys=True,
                               separators=(',', ':')).encode('utf-8')).hexdigest()
    check()
    if packet['source_sha256'] != digest:
        return False
    certificate = packet['certificate']
    if (type(certificate) is not dict or
            type(certificate.get('schema')) is not str or
            certificate['schema'] != 'pachner-cochain-endpoint-v1' or
            type(certificate.get('max_upward')) is not int or certificate['max_upward'] != 1 or
            certificate.get('disc_certificate') is not None or
            type(certificate.get('moves')) is not list or not 1 <= len(certificate['moves']) <= 3):
        return False
    upward = 0
    for index, step in enumerate(certificate['moves']):
        check()
        if type(step) is not dict or set(step) != {'triangulation', 'transport'}:
            return False
        after, transport = step['triangulation'], step['transport']
        if (type(after) is not dict or set(after) != {'tetrahedra'} or
                type(after['tetrahedra']) is not list or type(transport) is not dict or
                type(transport.get('schema')) is not str or
                transport['schema'] != 'pachner-cocycle-transport-v1'):
            return False
        count = len(after['tetrahedra'])
        last = index == len(certificate['moves'])-1
        if (last and count != n-1) or (not last and count < n):
            return False
        if (not _zeros(transport.get('heights'), count, 4, check) or
                not _zeros(transport.get('coordinates'), count, 7, check) or
                not _zeros([transport.get('bipyramid_heights')], 1, 5, check) or
                type(transport.get('euler_jump')) is not int or transport['euler_jump'] != 0 or
                type(transport.get('normal_disc_jump')) is not int or transport['normal_disc_jump'] != 0):
            return False
        move = transport.get('move')
        if type(move) is not dict or type(move.get('schema')) is not str:
            return False
        if move['schema'] == 'pachner-23-v1':
            upward += 1
        elif move['schema'] != 'pachner-32-v1':
            return False
    if upward > 1 or not _zeros(certificate.get('coordinates'), n-1, 7, check):
        return False
    # Independently validate the original finite manifold, every intermediate
    # source, exact move/transport maps and a connected original cover of size
    # at most six. Initial heights are constructed here, never trusted input.
    replay = inspect_pachner_descent(source, [[0]*4 for _ in range(n)], certificate,
                                    max_upward=1, check=check)
    if (replay is None or replay['upward_moves'] != upward or
            replay['downward_moves'] != upward+1 or replay['final_tetrahedra'] != n-1):
        return False
    return _same(packet['successor'], replay['triangulation'], check)
