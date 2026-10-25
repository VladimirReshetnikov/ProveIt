#!/usr/bin/env python3
"""Independent, standard-library collection of every delivered quartic.

This module imports no producer or inherited compiler.  It verifies finite
polynomial data, not the unbounded Diophantine equivalence theorem.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def demand(condition, message):
    if not condition:
        raise ValueError(message)

def read_terms(terms, n, max_degree):
    out = defaultdict(int)
    for coefficient, indices in terms:
        demand(type(coefficient) is int, "noninteger coefficient")
        demand(coefficient != 0, "explicit zero coefficient")
        demand(isinstance(indices, list), "indices must be a list")
        demand(all(type(i) is int and 0 <= i < n for i in indices), "invalid coordinate")
        demand(len(indices) <= max_degree, "degree exceeds declared limit")
        demand(indices == sorted(indices), "noncanonical monomial")
        out[tuple(indices)] += coefficient
    return {m:c for m,c in out.items() if c}

def collect(equation):
    demand(equation['domain'] == 'unrestricted integers', 'wrong witness domain')
    n = len(equation['variables'])
    demand(n > 0, 'empty coordinate list')
    rows = [read_terms(r['terms'], n, 2) for r in equation['residuals']]
    out = defaultdict(int)
    for row in rows:
        for m, a in row.items():
            for p, b in row.items():
                out[tuple(sorted(m+p))] += a*b
    polynomial = {m:c for m,c in out.items() if c}
    return rows, polynomial

def verify_pair(equation, expanded, advertised):
    n = len(equation['variables'])
    demand(type(expanded['variables']) is int and expanded['variables'] == n, 'expanded dimension mismatch')
    demand(expanded['domain'] == 'unrestricted integers', 'expanded domain mismatch')
    rows, actual = collect(equation)
    supplied = read_terms(expanded['terms'], n, 4)
    demand(actual == supplied, 'expanded polynomial differs from sum of squares')
    metrics = {
        'variables': n, 'rows': len(rows),
        'degree': max(map(len, actual)),
        'monomials': len(actual),
        'height': max(map(abs, actual.values())),
        'row_height': max(abs(c) for r in rows for c in r.values()),
    }
    for key, value in metrics.items():
        demand(advertised[key] == value, f'metric mismatch: {key}')
    demand(set(i for m in actual for i in m) == set(range(n)), 'unused final coordinate')
    demand(metrics['degree'] == 4, 'final degree is not exactly four')
    return metrics

def rejected(call):
    try:
        call()
    except (ValueError, KeyError, TypeError, IndexError):
        return True
    raise ValueError('deliberately corrupted polynomial was accepted')

def audit_directory(path):
    files = [path/'equation.json', path/'expanded_polynomial.json', path/'METRICS.json']
    equation, expanded, metrics = [json.loads(p.read_text()) for p in files]
    result = verify_pair(equation, expanded, metrics)
    changed = deepcopy(expanded)
    changed['terms'][0][0] += 1
    rejected(lambda: verify_pair(equation, changed, metrics))
    changed = deepcopy(equation)
    changed['residuals'][0]['terms'][0][0] += 1
    rejected(lambda: verify_pair(changed, expanded, metrics))
    changed = deepcopy(metrics)
    changed['variables'] += 1
    rejected(lambda: verify_pair(equation, expanded, changed))
    return {'profile':str(path.relative_to(ROOT)), 'metrics':result, 'negative_controls_rejected':3,
            'sha256':{p.name:sha256(p.read_bytes()).hexdigest() for p in files}}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    profiles = sorted((ROOT/'equations').rglob('equation.json'))
    demand(bool(profiles), 'no equation profiles found')
    receipt = {'status':'passed', 'scope':'exact finite polynomial checks',
               'results':[audit_directory(p.parent) for p in profiles]}
    text = json.dumps(receipt, indent=2, sort_keys=True)+'\n'
    if args.receipt:
        args.receipt.write_text(text)
    print(text)

if __name__ == '__main__':
    main()
