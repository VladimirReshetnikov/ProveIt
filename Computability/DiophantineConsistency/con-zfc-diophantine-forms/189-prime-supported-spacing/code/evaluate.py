#!/usr/bin/env python3
"""Evaluate the literal 209-variable integer polynomial on a supplied tuple."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def evaluate(point):
    if not isinstance(point, list) or len(point) != 209 or any(type(x) is not int for x in point):
        raise ValueError('Expected an array of exactly 209 integers')
    equation = json.loads((ROOT / 'equations/equation.json').read_text())
    values = []
    for row in equation['residuals']:
        total = 0
        for c, monomial in row['terms']:
            term = c
            for i in monomial:
                term *= point[i]
            total += term
        values.append(total)
    return sum(v * v for v in values), values


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('tuple', type=Path)
    parser.add_argument('--residuals', action='store_true')
    args = parser.parse_args()
    value, residuals = evaluate(json.loads(args.tuple.read_text()))
    result = {'polynomial_value': value, 'is_zero': value == 0}
    if args.residuals:
        result['residual_values'] = residuals
    print(json.dumps(result, indent=2))
