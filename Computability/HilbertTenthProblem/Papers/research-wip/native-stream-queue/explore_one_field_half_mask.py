#!/usr/bin/env python3
"""Exact 51-operation one-field mask module; no universal compiler claim."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

import sympy as sp

HERE = Path(__file__).resolve().parent
PAPERS = HERE.parents[1]
sys.path.insert(0, str(PAPERS / 'verification'))
import explore_fixed_raw_universal_76 as baseline

CORE = list(baseline.CORE)
CORE_NAMES = ['a', 'c', 'd', 'f', 'h', 'i', 'j', 'k', 'o', 'r',
              's', 'w', 'tau', 'eta', 'zeta', 'ga', 'y_aux']
NAMES = ['n', 'F', 'Jrep'] + CORE_NAMES
OUTER = [
    ('q', '*', 'n', 'n'),
    ('qm1', '-', 'q', 1),
    ('repunit', '*', 'Bm1', 'Jrep'),
    ('n2', '*', 'q', 'n'),
    ('mask', '*', 'm', 'Jrep'),
    ('gap', '-', 'q', 'F'),
    ('rproduct', '*', 'gap', 'qm1'),
    ('r_lhs', '+', 'rproduct', 'mask'),
]
SCHEDULE = OUTER + CORE
EQUALITIES = [('repunit', 'qm1'), ('r', 'r_lhs')] + baseline.EQUALITIES[5:15]


def run(rows, values):
    env = dict(values)
    for name, op, left, right in rows:
        assert name not in env, name
        x = env[left] if isinstance(left, str) else left
        y = env[right] if isinstance(right, str) else right
        env[name] = x * y if op == '*' else x + y if op == '+' else x - y
    return env


def sources(z):
    # Independent source polynomials, not copied from the evaluated registers.
    n, F, J = (z[v] for v in ('n', 'F', 'Jrep'))
    a, c, d, f, h, i, j, k, o, r, s, w, tau, eta, zeta, ga, ya = (
        z[v] for v in CORE_NAMES)
    q, D0 = n**2, n**3
    X, Y = w * D0, s * D0
    delta = a*a + 4*a + 3
    U = j*c - (2*r+1)
    return [
        (z['B']-1)*J - q + 1,
        r - (q-F)*(q-1) - z['m']*J,
        ((X*Y)**2 + X)*(k*Y)**2 - tau*(tau+1),
        c-k*Y-eta, k-eta-zeta, k-r-1-h*X*Y,
        a-Y*(X+1), d-X-a*c-ga*(4*a+3),
        d*d-1-delta*c*c,
        (i*c*c)**2-delta*(f*f-1),
        delta*(f*f-1)*(U*U-ya*ya)-(1-ya*ya),
        U-o*f+c,
    ]


def source_audit():
    z = {v: sp.Symbol(v, positive=True, integer=True) for v in NAMES+['B', 'm']}
    env = run(SCHEDULE, dict(z, Bm1=z['B']-1))
    polynomials = [sp.expand(p) for p in sources(z)]
    U = z['j']*z['c']-(2*z['r']+1)
    correction = polynomials[9]*(U*U-z['y_aux']**2)
    records = []
    for index, ((left, right), source) in enumerate(zip(EQUALITIES, polynomials)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if index == 10 else 0
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, index
        records.append(dict(index=index, equality=[left, right], source_sign=sign,
                            source=str(source), correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in SCHEDULE)
    assert counts['*'] == 30 and counts['+']+counts['-'] == 21
    assert len(SCHEDULE) == 51 and len(EQUALITIES) == len(polynomials) == 12
    assert len(NAMES) == 20 and len(set(NAMES)) == 20
    assert set().union(*(p.free_symbols for p in polynomials)) == set(z.values())
    assert CORE == baseline.CORE and len(CORE) == 43
    assert sp.expand(env['n2']-z['n']**3) == 0
    return dict(operations=51, multiplications=30, additions_subtractions=21,
                parameters=['n>0', 'F>0'], positive_witnesses=['Jrep']+CORE_NAMES,
                positive_witness_count=18, equations=12,
                schedule=[list(row) for row in SCHEDULE], sources=records,
                ledger=dict(outer=8, retained_kernel=43),
                scope='Complete bounded mask module; universal compiler absent')


def fixed_masks(d):
    return [m for m in range(1, (1 << d)-1, 2) if m.bit_count() == d//2]


def finite_masks():
    counts = Counter()
    examples = []
    for d, N in [(6, 1), (6, 2), (8, 1), (8, 2), (10, 1)]:
        B, q = 1 << d, 1 << (d*N)
        J = (q-1)//(B-1)
        threshold = 3*d*N//2
        masks = fixed_masks(d)
        if N == 2:
            masks = masks[::max(1, len(masks)//5)]
        for m in masks:
            M = m*J
            assert M.bit_count() == d*N//2 and M & 1
            for F in range(1, q):
                r = (q-F)*(q-1)+M
                mask_ok = F & M == 0
                assert q <= r < q*q
                assert r.bit_count() <= threshold
                assert (r.bit_count() >= threshold) == mask_ok
                counts['bounded_fields'] += 1
                counts['overflow_fields'] += F+M >= q
                if mask_ok:
                    assert F % 2 == 0 and r % 2 == 1
                    assert (q**3) < r**4
                    counts['valid_positive_fields'] += 1
            boundary_r = M
            assert boundary_r.bit_count() < threshold
            counts['boundary_valuation_exclusions'] += 1
            if len(examples) < 8:
                examples.append(dict(d=d, N=N, m=m, boundary_r=boundary_r,
                                     boundary_valuation=boundary_r.bit_count(),
                                     required_valuation=threshold))
    return dict(counts, examples=examples,
                full_pell_coordinates_materialized=False)


def pre_power_bounds():
    counts = Counter()
    for d in (6, 8):
        B = 1 << d
        for n in range(1, 513):
            q = n*n
            if q < B or (q-1) % (B-1):
                continue
            J = (q-1)//(B-1)
            for m in fixed_masks(d):
                M = m*J
                assert 7 <= m <= M < q-1
                for F in sorted({1, 2, q//2, q-1, q, q+1, 2*q}):
                    r = (q-F)*(q-1)+M
                    counts['arbitrary_square_tuples'] += 1
                    if r <= 0:
                        assert F > q
                        continue
                    assert F <= q and 7 <= r < q*q
                    D0 = n**3
                    X = Y = D0  # These minimize all required lower bounds.
                    a = Y*(X+1)
                    assert D0 >= 512 and D0*D0 == q**3
                    assert X*Y > r+1 and a > 2*r+1 and 8*r < a
                    counts['positive_indices'] += 1
                    counts['pre_power_endpoint_cases'] += F == q
                    counts['nonpower_square_cases'] += bool(q & (q-1))
    # Check the small-index growth implications without enormous Pell powers.
    for A in range(2, 200):
        assert (2*A-1)**8 > A*(A*A-1)**2
    for r in range(7, 256):
        assert 8*64**r < 512**(r+1)
        assert 2**(2*r+1) > 32*r
    return dict(counts)


def verify():
    dependencies = [
        PAPERS/'1980/BASE_TWO_PELL_89_PROOF.md',
        PAPERS/'1980/HALF_PARAMETER_PELL_92_PROOF.md',
        PAPERS/'1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md',
        PAPERS/'1980/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md',
        PAPERS/'verification/explore_fixed_raw_universal_76.py',
    ]
    return dict(status='PASS_ONE_FIELD_HALF_MASK_51_MODULE', source=source_audit(),
                finite_masks=finite_masks(), pre_power=pre_power_bounds(),
                dependency_lf_sha256={str(p.relative_to(PAPERS)):
                    hashlib.sha256(p.read_bytes().replace(b'\r\n', b'\n')).hexdigest()
                    for p in dependencies},
                scope='Symbolic source and finite corroboration of a mask theorem; no universal certificate')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert result == json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'], result['source']['operations'])
    print(result['finite_masks'])
    print(result['pre_power'])
