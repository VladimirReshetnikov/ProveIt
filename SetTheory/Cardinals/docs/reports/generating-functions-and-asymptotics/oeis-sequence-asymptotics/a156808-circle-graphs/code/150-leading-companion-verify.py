#!/usr/bin/env python3
"""Recompute all evidence and reject changed, missing, or additional fields."""
from pathlib import Path
import argparse
import json
import sys

from circle_companion import ROOT, build_evidence
from safe_io import regular_bytes


class VerificationError(ValueError):
    pass


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise VerificationError('Duplicate JSON key: ' + key)
        out[key] = value
    return out


def invalid_constant(value):
    raise VerificationError('Nonfinite JSON value: ' + value)


def load_document(path):
    return json.loads(regular_bytes(path), object_pairs_hook=unique_object, parse_constant=invalid_constant)


def compare(actual, expected, path='$'):
    # Equality alone is not sufficient: Python considers True == 1 == 1.0.
    if type(actual) is not type(expected):
        raise VerificationError(path + ': wrong type')
    if isinstance(expected, dict):
        if set(actual) != set(expected):
            raise VerificationError(path + ': missing or additional keys')
        for key in sorted(expected):
            compare(actual[key], expected[key], path + '.' + key)
    elif isinstance(expected, list):
        if len(actual) != len(expected):
            raise VerificationError(path + ': wrong list length')
        for index, (found, wanted) in enumerate(zip(actual, expected)):
            compare(found, wanted, path + '[' + str(index) + ']')
    elif actual != expected:
        raise VerificationError(path + ': value differs from exact recomputation')


def verify_document(document):
    compare(document, build_evidence())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('evidence', nargs='?', type=Path, default=ROOT/'evidence.json')
    args = parser.parse_args()
    try:
        verify_document(load_document(args.evidence))
    except (ValueError, OSError, TypeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        return 1
    print('PASS: every evidence field matches fresh exact computation')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
