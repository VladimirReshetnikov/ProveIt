#!/usr/bin/env python3
"""Evaluate a supplied tuple in the literal Balanced218 or Centered216 polynomial."""
import argparse
import json
from pathlib import Path
import sys

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('endpoint', choices=('218', '216'))
    ap.add_argument('values', help='JSON array filename, or - for stdin')
    ap.add_argument('--residuals', action='store_true')
    args = ap.parse_args()
    values = json.load(sys.stdin) if args.values == '-' else json.loads(Path(args.values).read_text())
    n = int(args.endpoint)
    if type(values) is not list or len(values) != n or any(type(x) is not int for x in values):
        raise ValueError(f'Expected exactly {n} unrestricted integers')
    eq = json.loads((Path(__file__).resolve().parent / f'equation{n}.json').read_text())
    result = []
    for row in eq['residuals']:
        v = 0
        for c, mon in row['terms']:
            term = c
            for i in mon:
                term *= values[i]
            v += term
        result.append(v)
    out = {'value':sum(v*v for v in result), 'variables':n}
    if args.residuals:
        out['residuals'] = result
    print(json.dumps(out))

if __name__ == '__main__':
    main()
