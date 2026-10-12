"""Exact JSON transport for binary integers without decimal-limit changes."""
import re


def encoded_integer(value):
    """Accept a literal integer or an explicitly signed hexadecimal string."""
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r'[+-]?0[xX][0-9a-fA-F]+', value):
        return int(value, 16)
    raise ValueError('integer fields require integers or signed hexadecimal strings')


def json_safe(value):
    """Encode large values and integer dictionary keys exactly.

    Dictionary keys become strings, as in ordinary JSON. Small integer keys
    retain their decimal form; large keys use hex too. This is transport,
    not a certificate verifier. No process-wide conversion setting changes.
    """
    if type(value) is int:
        return hex(value) if value.bit_length() > 4096 else value
    if isinstance(value, dict):
        result = {}
        for key, item in value.items():
            if type(key) is int:
                key = hex(key) if key.bit_length() > 4096 else str(key)
            if not isinstance(key, str) or key in result:
                raise ValueError('JSON keys must have distinct string encodings')
            result[key] = json_safe(item)
        return result
    if isinstance(value, (list, tuple)):
        return [json_safe(item) for item in value]
    return value


def certificate_equal(actual, expected):
    """Compare an exact schema, decoding only its specified integer fields."""
    if type(expected) is int:
        try:
            return encoded_integer(actual) == expected
        except ValueError:
            return False
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(
            certificate_equal(actual[key], item) for key, item in expected.items())
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(
            certificate_equal(a, e) for a, e in zip(actual, expected))
    return actual == expected


def decode_degree_profile(profile):
    """Restore a serialized tail profile to Python integers, without expansion.

    This validates the transport schema, not the mathematical homology claim.
    Pass the result to the ordinary profile query/rank/expansion helpers.
    """
    if not isinstance(profile, dict) or set(profile) != {'points', 'intervals'}:
        raise ValueError('expected points and intervals')
    if not isinstance(profile['points'], dict) or not isinstance(profile['intervals'], list):
        raise ValueError('invalid degree profile containers')
    points = {}
    for key, value in profile['points'].items():
        if isinstance(key, str) and re.fullmatch(r'-?(0|[1-9][0-9]*)', key):
            degree = int(key)
        else:
            degree = encoded_integer(key)
        if degree in points:
            raise ValueError('duplicate degree after decoding')
        points[degree] = encoded_integer(value)
    intervals = []
    for piece in profile['intervals']:
        if not isinstance(piece, dict) or set(piece) != {'start', 'end', 'dimension'}:
            raise ValueError('invalid constant interval')
        intervals.append({key: encoded_integer(value) for key, value in piece.items()})
    return {'points': points, 'intervals': intervals}
