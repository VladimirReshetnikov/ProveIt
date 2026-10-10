#!/usr/bin/env python3
"""Independent raw-row expansion of frozen certificates.

Does NOT call Distribution, its straightener, its basis selector, or its
certificate generator. It shares only integer polynomial arithmetic.
"""
from pathlib import Path
import json
from math import isqrt
from distribution import Poly, add_scaled

ROOT = Path(__file__).resolve().parents[1]

def verify_record(rec: dict) -> dict:
    q, a = rec['level'], rec['point_index']
    if type(q) is not int or q < 2 or type(a) is not int or not 0 <= a < q:
        raise ValueError('invalid level or point')
    ps = tuple(p for p in range(2, q+1) if q % p == 0
               and all(p % d for d in range(2, isqrt(p)+1)))
    if rec['prime_order'] != list(ps):
        raise ValueError('wrong prime order')
    arity = len(ps)
    one = Poly.constant(arity, 1)
    A = {p: Poly.variable(arity, i) for i, p in enumerate(ps)}
    residual = {a: one}
    seen = set()
    for item in rec['normal_form']:
        b = item['point']
        if type(b) is not int or not 0 <= b < q or b in seen:
            raise ValueError('invalid or duplicate normal-form point')
        seen.add(b)
        add_scaled(residual, {b: one}, -Poly.decode(arity, item['polynomial']))
    row_seen = set()
    for item in rec['row_combination']:
        p, x = item['prime'], item['target']
        if p not in ps or type(x) is not int or not 0 <= x < q or x % p:
            raise ValueError('invalid row')
        if (p, x) in row_seen:
            raise ValueError('duplicate row')
        row_seen.add((p, x))
        coeff = Poly.decode(arity, item['polynomial'])
        # Subtract coeff * (sum_(p*y=x) e_y - A_p e_x).
        for y in range(q):
            if p * y % q == x:
                add_scaled(residual, {y: one}, -coeff)
        add_scaled(residual, {x: one}, coeff * A[p])
    if residual:
        raise AssertionError(f'Nonzero polynomial certificate residual at level {q}')
    return {'level': q, 'point_index': a, 'rows': len(row_seen),
            'exact_residual': 0}

def main():
    obj = json.loads((ROOT/'data/identity_certificates.json').read_text())
    if obj.get('schema') != 'weighted-distribution-certificate-v1':
        raise ValueError('unsupported schema')
    out = [verify_record(rec) for rec in obj['records']]
    # A deterministic corruption must fail; this is not an independence test.
    bad = json.loads(json.dumps(obj['records'][1]))
    bad['normal_form'][0]['polynomial'][0][1] += 1
    try:
        verify_record(bad)
    except AssertionError:
        corrupted_rejected = True
    else:
        raise AssertionError('corrupted certificate was accepted')
    result = {'certificates': out, 'corrupted_certificate_rejected': corrupted_rejected}
    (ROOT/'logs/certificate_replay.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
