#!/usr/bin/env python3
"""Evaluate the certified integer maps for radical and affine projections.

The maps are inverse on zero sets, as established by PROJECTION_PROOF.md
and independently checked projection certificates. This is an evaluator,
not a search for a zero or a proof that the input tuple is a zero.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def evaluate(terms, point):
    result = 0
    for coefficient, monomial in terms:
        term = coefficient
        for coordinate in monomial:
            term *= point[coordinate]
        result += term
    return result


def radical_project(point, step):
    direction = dict(step['direction'])
    p = step['pivot']
    if direction.get(p) != 1 or len(point) != len(step['retained_old_indices']) + 1:
        raise ValueError('Incorrect radical map dimension or pivot')
    t = point[p]
    return [point[i] - direction.get(i, 0) * t for i in step['retained_old_indices']]


def radical_lift(point, step):
    direction = dict(step['direction'])
    p = step['pivot']
    keep = step['retained_old_indices']
    if direction.get(p) != 1 or len(point) != len(keep):
        raise ValueError('Incorrect radical map dimension or pivot')
    y = [0] * (len(keep) + 1)
    for old, value in zip(keep, point):
        y[old] = value
    t = evaluate(step['sheared_pivot_solution'], y)
    return [value + direction.get(i, 0) * t for i, value in enumerate(y)]


def affine_project(point, certificate):
    p = certificate['eliminated_coordinate']
    return point[:p] + point[p+1:]


def affine_lift(point, certificate):
    p = certificate['eliminated_coordinate']
    y = point[:p] + [0] + point[p:]
    y[p] = evaluate(certificate['restoration_terms_original_indices'], y)
    return y


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('direction', choices=['lift', 'project'])
    ap.add_argument('radical_certificate', type=Path)
    ap.add_argument('point', type=Path, help='JSON array of integer coordinates')
    ap.add_argument('--affine-certificate', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    radical = json.loads(args.radical_certificate.read_text())
    point = json.loads(args.point.read_text())
    if not isinstance(point, list) or not all(type(v) is int for v in point):
        raise ValueError('Point must be a JSON array of integers')
    affine = json.loads(args.affine_certificate.read_text()) if args.affine_certificate else None
    if args.direction == 'lift':
        if affine is not None:
            point = affine_lift(point, affine)
        for step in reversed(radical['steps']):
            point = radical_lift(point, step)
    else:
        for step in radical['steps']:
            point = radical_project(point, step)
        if affine is not None:
            point = affine_project(point, affine)
    encoded = json.dumps(point, separators=(',', ':')) + '\n'
    if args.output:
        args.output.write_text(encoded)
    else:
        print(encoded, end='')


if __name__ == '__main__':
    main()
