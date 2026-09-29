#!/usr/bin/env python3
"""Compare an enumerator CSV with every corresponding archived count.

Accepts complete prefixes of sizes 1..N, 1 <= N <= 18. The default reference
is data/profiles.json. This is a reproducibility check, not a proof of the
geometric recurrence or of the enumeration algorithm.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parent.parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('csv', type=Path, help='CSV produced by either C++ enumerator')
    parser.add_argument('--reference', type=Path, default=BASE / 'data/profiles.json')
    args = parser.parse_args()
    try:
        data = json.loads(args.reference.read_text(encoding='utf-8'))
        expected_header = ['n', 'A'] + data['names']
        with args.csv.open(newline='', encoding='utf-8') as stream:
            reader = csv.reader(stream)
            header = next(reader, None)
            if header != expected_header:
                raise ValueError(f'Header mismatch: expected {expected_header!r}, got {header!r}')
            size = 0
            for size, row in enumerate(reader, start=1):
                if size >= len(data['polyominoes']):
                    raise ValueError('CSV exceeds the reference prefix')
                if len(row) != len(expected_header):
                    raise ValueError(f'Wrong number of columns on data row {size}')
                actual = [int(value) for value in row]
                expected = [size, data['polyominoes'][size]] + [
                    values[size] for values in data['counts']
                ]
                for column, a, b in zip(expected_header, actual, expected):
                    if a != b:
                        raise ValueError(f'Size {size}, column {column}: {a} != {b}')
            if size == 0:
                raise ValueError('CSV has no data rows')
        print(f'MATCH: sizes 1..{size}; {size} unmarked and {17 * size} marked counts.')
        return 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f'CHECK FAILED: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
