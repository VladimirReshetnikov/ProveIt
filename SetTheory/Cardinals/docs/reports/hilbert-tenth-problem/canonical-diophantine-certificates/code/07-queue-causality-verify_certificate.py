#!/usr/bin/env python3
"""Independent parser/evaluator for exported integer polynomial certificates.
Does not import the compiler.  Verifies a supplied witness, not unsatisfiability.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def verify(data: dict) -> dict:
    if data.get('format') != 'integer-polynomial-circuit-v1' or data.get('combination') != 'sum_of_squares':
        raise ValueError('unsupported certificate format')
    names = data['variables']
    if len(set(names)) != len(names):
        raise ValueError('duplicate variables')
    w = [int(x) for x in data['witness']]
    if len(w) != len(names) or any(x < 0 for x in w):
        raise ValueError('invalid natural witness')
    values, degrees = [], []
    for index, node in enumerate(data['nodes']):
        op = node['op']
        if op == 'var':
            j = node['index']
            if type(j) is not int or not 0 <= j < len(w):
                raise ValueError('invalid variable reference')
            v, d = w[j], 1
        elif op == 'const':
            v, d = int(node['value']), 0
        elif op in ('add', 'sub', 'mul'):
            a, b = node['args']
            if any(type(j) is not int or not 0 <= j < index for j in (a, b)):
                raise ValueError('the circuit is not topologically ordered')
            if op == 'add':
                v, d = values[a]+values[b], max(degrees[a], degrees[b])
            elif op == 'sub':
                v, d = values[a]-values[b], max(degrees[a], degrees[b])
            else:
                v, d = values[a]*values[b], degrees[a]+degrees[b]
        else:
            raise ValueError(f'unsupported operation: {op}')
        values.append(v); degrees.append(d)
    roots = data['residual_roots']
    if any(type(i) is not int or not 0 <= i < len(values) for i in roots):
        raise ValueError('invalid residual reference')
    residuals = [values[i] for i in roots]
    degree = 2*max((degrees[i] for i in roots), default=0)
    if degree > data['degree_upper_bound']:
        raise ValueError('false degree bound')
    return {'accepted': all(r == 0 for r in residuals), 'energy': str(sum(r*r for r in residuals)),
            'variables': len(w), 'residuals': len(roots), 'degree_upper_bound': degree,
            'nonzero_residuals': [i for i,r in enumerate(residuals) if r]}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', type=Path)
    args = p.parse_args()
    result = verify(json.loads(args.certificate.read_text(encoding='utf8')))
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
