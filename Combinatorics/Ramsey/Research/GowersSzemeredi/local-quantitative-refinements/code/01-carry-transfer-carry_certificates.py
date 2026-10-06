#!/usr/bin/env python3
"""Enumerate fractional carry patterns using independently checked rational certificates.

Generate (requires NumPy and SciPy):
  python code/carry_certificates.py generate --max-k 4 --out certificates/carry.json
Verify (Python standard library only):
  python code/carry_certificates.py verify certificates/carry.json

The numerical optimizer only proposes certificates. Every accepted branch is
checked using Fraction. Positive primal slack proves strict feasibility;
nonnegative dual multipliers prove strict infeasibility. No tolerance enters
the verifier. The full branch tree is checked, not just the final count.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
from typing import Any


def hyperplanes(k: int) -> list[tuple[list[int], int]]:
    out = []
    for mask in range(1, 1 << k):
        v = [(mask >> i) & 1 for i in range(k)]
        for j in range(1, sum(v)):
            out.append((v, j))
    return out


def constraints(k: int, signs: str) -> tuple[list[list[int]], list[int]]:
    """A (x,epsilon) <= b; epsilon>0 encodes all strict inequalities."""
    A, b = [], []
    for i in range(k):
        v = [0] * (k + 1)
        v[i], v[-1] = -1, 1
        A.append(v); b.append(0)
        v = [0] * (k + 1)
        v[i], v[-1] = 1, 1
        A.append(v); b.append(1)
    H = hyperplanes(k)
    if len(signs) > len(H) or any(s not in '01' for s in signs):
        raise ValueError('Invalid sign word')
    for bit, (v, j) in zip(signs, H):
        if bit == '0':  # v.x < j
            A.append(v + [1]); b.append(j)
        else:           # v.x > j
            A.append([-x for x in v] + [1]); b.append(-j)
    return A, b


def dot(a: list[Any], b: list[Any]) -> F:
    return sum((F(x) * F(y) for x, y in zip(a, b)), F(0))


def check_record(k: int, rec: dict[str, Any]) -> bool:
    A, b = constraints(k, rec['signs'])
    if rec['kind'] == 'primal':
        z = [F(s) for s in rec['certificate']]
        if len(z) != k + 1 or z[-1] <= 0:
            raise ValueError('Invalid positive-slack certificate')
        if not all(dot(row, z) <= rhs for row, rhs in zip(A, b)):
            raise ValueError('Primal inequality failed')
        return True
    if rec['kind'] == 'dual':
        lam = [F(s) for s in rec['certificate']]
        if len(lam) != len(A) or any(x < 0 for x in lam):
            raise ValueError('Invalid dual coefficients')
        target = [F(0)] * k + [F(1)]
        actual = [sum((lam[i] * A[i][j] for i in range(len(A))), F(0))
                  for j in range(k + 1)]
        if actual != target or dot(lam, b) > 0:
            raise ValueError('Dual identity failed')
        return False
    raise ValueError('Unknown certificate kind')


def solve(k: int, signs: str) -> dict[str, Any]:
    import numpy as np
    from scipy.optimize import linprog
    A, b = constraints(k, signs)
    cost = [0] * k + [-1]
    result = linprog(cost, A_ub=np.asarray(A, dtype=float),
                     b_ub=np.asarray(b, dtype=float),
                     bounds=[(None, None)] * (k + 1), method='highs')
    if not result.success:
        raise RuntimeError(f'Optimizer failed for k={k}, signs={signs}: {result.message}')
    # Rational reconstruction is only a proposal; the exact checks are decisive.
    primal = result.x[-1] > 1e-9
    vec = result.x if primal else -result.ineqlin.marginals
    for bound in (10_000, 1_000_000, 100_000_000):
        rec = {'signs': signs, 'kind': 'primal' if primal else 'dual',
               'certificate': [str(F(float(x)).limit_denominator(bound)) for x in vec]}
        try:
            check_record(k, rec)
            return rec
        except ValueError:
            pass
    raise RuntimeError(f'Could not reconstruct exact certificate for {k=}, {signs=}')


def generate(max_k: int) -> dict[str, Any]:
    if not 1 <= max_k <= 5:
        raise ValueError('Use 1 <= max-k <= 5 (cost rises rapidly).')
    all_data = {'format': 'carry-strict-LP-certificates-v1', 'dimensions': []}
    for k in range(1, max_k + 1):
        H = hyperplanes(k)
        root = solve(k, '')
        if not check_record(k, root):
            raise RuntimeError('Open cube must be feasible')
        records = [root]
        active = ['']
        layer_counts = [1]
        for depth in range(len(H)):
            nxt = []
            for s in active:
                for bit in '01':
                    rec = solve(k, s + bit)
                    records.append(rec)
                    if check_record(k, rec):
                        nxt.append(s + bit)
            active = nxt
            layer_counts.append(len(active))
        data = {'k': k, 'hyperplane_count': len(H), 'count': len(active),
                'layer_counts': layer_counts, 'records': records}
        all_data['dimensions'].append(data)
        print(f'k={k}: C_k={len(active)}, hyperplanes={len(H)}, certificates={len(records)}', flush=True)
    return all_data


def verify(data: dict[str, Any]) -> list[dict[str, int]]:
    if data.get('format') != 'carry-strict-LP-certificates-v1':
        raise ValueError('Unsupported format')
    reports = []
    seen_dimensions = set()
    for dim in data['dimensions']:
        k = dim['k']
        if k in seen_dimensions or not isinstance(k, int) or k < 1:
            raise ValueError('Invalid or duplicate dimension')
        seen_dimensions.add(k)
        H = hyperplanes(k)
        if dim['hyperplane_count'] != len(H):
            raise ValueError('Wrong hyperplane count')
        by_sign = {}
        for rec in dim['records']:
            s = rec['signs']
            if s in by_sign:
                raise ValueError('Duplicate branch')
            by_sign[s] = rec
        if '' not in by_sign or not check_record(k, by_sign['']):
            raise ValueError('Missing feasible root')
        seen = {''}
        active = ['']
        layer_counts = [1]
        for _ in H:
            nxt = []
            for s in active:
                for bit in '01':
                    word = s + bit
                    if word not in by_sign:
                        raise ValueError('Missing branch; enumeration is not exhaustive')
                    seen.add(word)
                    if check_record(k, by_sign[word]):
                        nxt.append(word)
            active = nxt
            layer_counts.append(len(active))
        if seen != set(by_sign):
            raise ValueError('Extraneous or unreachable branches')
        if dim['count'] != len(active) or dim['layer_counts'] != layer_counts:
            raise ValueError('Incorrect counts')
        reports.append({'k': k, 'count': len(active), 'hyperplanes': len(H),
                        'certificates': len(seen)})
    return reports


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='command', required=True)
    gen = sub.add_parser('generate')
    gen.add_argument('--max-k', type=int, default=4)
    gen.add_argument('--out', type=Path, required=True)
    ver = sub.add_parser('verify')
    ver.add_argument('file', type=Path)
    args = ap.parse_args()
    if args.command == 'generate':
        data = generate(args.max_k)
        reports = verify(data)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(data, separators=(',', ':')) + '\n', encoding='utf-8')
    else:
        data = json.loads(args.file.read_text(encoding='utf-8'))
        reports = verify(data)
    print(json.dumps({'verified': True, 'dimensions': reports}, indent=2))


if __name__ == '__main__':
    main()
