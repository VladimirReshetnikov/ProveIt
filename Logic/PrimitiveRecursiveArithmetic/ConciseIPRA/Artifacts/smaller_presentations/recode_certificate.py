"""Untrusted recoding helper for the documented supply certificate protocol.

The checker is standalone and does not import this module. Numerical zero
in expression fields becomes 1; administrative false markers remain 0 or [].
"""
import json
from pathlib import Path


def expression(tree):
    if type(tree) is list:
        return [expression(child) for child in tree]
    return 1 if type(tree) is int and tree == 0 else tree


def packet(record):
    if type(record) is not list or len(record) != 4:
        return record
    major, source, seed, body = record
    if major:
        if type(major) is list and len(major) in (2, 3):
            # Equality transport, or closure elimination at source marker 0.
            source = source if not source else expression(source)
            return [expression(major), source, expression(seed), expression(body)]
        # Witness discharge has no meaningful term fields in canonical packets.
        return [expression(major), source, seed, body]
    if seed:
        # A computation supply; its zero-counter flag remains false-valued.
        return [major, source if not source else expression(source),
                expression(seed), expression(body)]
    # Introduction: seed is the progress/case marker 0 or [], body a witness.
    return [major, source, seed, expression(body)]


def convert(certificate):
    if type(certificate) is not list or not certificate:
        return certificate
    return [packet(record) for record in certificate[:-1]] + [expression(certificate[-1])]


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('target', type=Path)
    args = parser.parse_args()
    args.target.write_text(json.dumps(convert(json.loads(args.source.read_text())),
                                     separators=(',', ':')) + '\n')
