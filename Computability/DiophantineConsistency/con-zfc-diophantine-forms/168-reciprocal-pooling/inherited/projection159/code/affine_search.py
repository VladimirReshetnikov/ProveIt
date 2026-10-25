#!/usr/bin/env python3
"""Exact constant-row-combination search for hidden affine consequences.

Each output relation is checked directly against the input sparse residuals.
Uses Fraction arithmetic only, with no external dependencies.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
from functools import reduce
from hashlib import sha256
from math import gcd, lcm
from pathlib import Path
import json


def add_scaled(dst, src, factor):
    for k, v in src.items():
        nv = dst.get(k, 0) + factor * v
        if nv:
            dst[k] = nv
        else:
            dst.pop(k, None)


def integral_pair(poly, combo):
    den = lcm(*(v.denominator for v in list(poly.values()) + list(combo.values())))
    pp = {k: int(v * den) for k, v in poly.items()}
    cc = {k: int(v * den) for k, v in combo.items()}
    g = reduce(gcd, (abs(v) for v in list(pp.values()) + list(cc.values())), 0)
    if g:
        pp = {k: v // g for k, v in pp.items()}
        cc = {k: v // g for k, v in cc.items()}
    return pp, cc


def run(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    rows = [{tuple(m): Fraction(c) for c, m in r['terms'] if c} for r in data['residuals']]
    basis = {}
    zero = []
    for i, full in enumerate(rows):
        quad = {k: v for k, v in full.items() if len(k) == 2}
        poly = dict(full)
        combo = {i: Fraction(1)}
        while quad:
            pivot = min(quad)
            if pivot not in basis:
                a = quad[pivot]
                basis[pivot] = (
                    {k: v / a for k, v in quad.items()},
                    {k: v / a for k, v in poly.items()},
                    {k: v / a for k, v in combo.items()},
                )
                break
            q, p, c = basis[pivot]
            a = quad[pivot]
            add_scaled(quad, q, -a)
            add_scaled(poly, p, -a)
            add_scaled(combo, c, -a)
        if not quad:
            if any(len(k) > 1 for k in poly):
                raise RuntimeError('Quadratic elimination failed')
            p, c = integral_pair(poly, combo)
            check = {}
            for j, a in c.items():
                add_scaled(check, rows[j], a)
            if check != p:
                raise RuntimeError('Certificate identity failed')
            g = reduce(gcd, (abs(v) for k, v in p.items() if k), 0)
            content = reduce(gcd, (abs(v) for v in p.values()), 0)
            zero.append({
                'affine_terms': [[v, list(k)] for k, v in sorted(p.items())],
                'row_combination': [[v, j] for j, v in sorted(c.items())],
                'linear_gcd': g,
                'whole_content': content,
                'primitive_linear_gcd': g // content if content else 0,
                'unit_variables_after_content_normalization': [k[0] for k, v in p.items() if len(k)==1 and content and abs(v)==content],
            })
    return {
        'schema': 'exact-hidden-affine-row-combinations-v1',
        'input_path': str(path.resolve()),
        'input_sha256': sha256(raw).hexdigest(),
        'variables': len(data['variables']),
        'residuals': len(rows),
        'quadratic_monomials': len(set(k for r in rows for k in r if len(k)==2)),
        'quadratic_row_rank': len(basis),
        'quadratic_left_nullity': len(rows)-len(basis),
        'certified_relations': zero,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('input', nargs='+', type=Path)
    ap.add_argument('--output-dir', type=Path, required=True)
    args = ap.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for p in args.input:
        result = run(p)
        output = args.output_dir / (p.parent.name + '_affine_search.json')
        output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps({k: v for k, v in result.items() if k != 'certified_relations'}), flush=True)
        for relation in result['certified_relations']:
            print(json.dumps(relation), flush=True)


if __name__ == '__main__':
    main()

