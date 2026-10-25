#!/usr/bin/env python3
"""Evaluate a delivered direct equation at a supplied integer tuple."""
import argparse
import json
from pathlib import Path
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parent


def polynomial(terms, point):
    total = 0
    for coefficient, indices in terms:
        value = coefficient
        for i in indices:
            value *= point[i]
        total += value
    return total


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('point', type=Path, help='JSON array of integer coordinates')
    p.add_argument('--equation', type=Path, default=ROOT/'direct/equations/principal239/natural/equation.json')
    p.add_argument('--integer-companion', action='store_true', help='Use three signed coordinates per natural coordinate')
    args = p.parse_args()
    data = json.loads(args.equation.read_text())
    point = json.loads(args.point.read_text())
    n = len(data['variables'])
    if not isinstance(point, list) or not all(type(x) is int for x in point):
        raise ValueError('Point must be a JSON array of integers')
    if args.integer_companion:
        if len(point) != 3*n:
            raise ValueError('Expected ' + str(3*n) + ' signed coordinates')
        point = [a*a+b*b+c*(c+1) for a,b,c in zip(point[::3], point[1::3], point[2::3])]
    elif len(point) != n or any(x < 0 for x in point):
        raise ValueError('Expected ' + str(n) + ' nonnegative coordinates')
    values = [polynomial(row['terms'], point) for row in data['residuals']]
    result = sum(x*x for x in values)
    print(json.dumps({'value':result, 'is_zero':result == 0,
                      'nonzero_residuals':sum(x != 0 for x in values)}))


if __name__ == '__main__':
    main()
