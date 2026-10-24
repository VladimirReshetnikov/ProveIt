#!/usr/bin/env python3
"""Exact evaluation of a delivered residual equation or integer companion.

Usage: python3 code/evaluate_equation.py EQUATION_JSON POINT_JSON
POINT_JSON is a JSON array of integers in the equation's declared order.
This evaluates a specified point; it is not a solvability algorithm.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math


def evaluate_residuals(equation, point):
    if len(point) != len(equation['variables']):
        raise ValueError('Wrong number of coordinates')
    if any(type(v) is not int or v < 0 for v in point):
        raise ValueError('The base equation requires nonnegative integers')
    residuals = [sum(c * math.prod(point[i] for i in monomial)
                     for c, monomial in row['terms'])
                 for row in equation['residuals']]
    return sum(r * r for r in residuals)


def evaluate(path, point):
    data = json.loads(path.read_text())
    if data.get('schema') == 'literal_three_square_domain_substitution_v1':
        if len(point) != data['variables'] or any(type(v) is not int for v in point):
            raise ValueError('The companion requires the declared number of integer coordinates')
        base = (path.parent / data['base_equation']).resolve()
        if hashlib.sha256(base.read_bytes()).hexdigest() != data['base_equation_sha256']:
            raise ValueError('Base equation hash mismatch')
        mapped = [point[3*i] ** 2 + point[3*i+1] ** 2 + point[3*i+2] * (point[3*i+2] + 1)
                  for i in range(data['source_variables'])]
        return evaluate_residuals(json.loads(base.read_text()), mapped)
    return evaluate_residuals(data, point)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('equation', type=Path)
    p.add_argument('point', type=Path)
    a = p.parse_args()
    print(evaluate(a.equation, json.loads(a.point.read_text())))


if __name__ == '__main__':
    main()
