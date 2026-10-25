#!/usr/bin/env python3
"""Independent whole-row audit of the five semantic source changes.

Does not import the mutation producer or its polynomial implementation.
Usage: python3 audit_changed_source.py PARENT_RAW CHILD_RAW [RECEIPT]
"""
from collections import defaultdict
from pathlib import Path
import hashlib
import json
import sys


def fail_unless(ok, message):
    if not ok:
        raise ValueError(message)


def clean(p):
    return {m: c for m, c in p.items() if c}


def poly(terms):
    out = defaultdict(int)
    for c, m in terms:
        out[tuple(sorted(m))] += c
    return clean(out)


def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for m, c in p.items():
            out[m] += c
    return clean(out)


def scale(p, k):
    return clean({m: k*c for m, c in p.items()})


def mul(p, q):
    out = defaultdict(int)
    for m, c in p.items():
        for n, d in q.items():
            out[tuple(sorted(m+n))] += c*d
    return clean(out)


def sq(p):
    return mul(p, p)


def var(i):
    return {(i,): 1}


def const(n):
    return {(): n} if n else {}


def substitute(p, replacements):
    result = {}
    for monomial, coefficient in p.items():
        term = const(coefficient)
        for i in monomial:
            term = mul(term, replacements.get(i, var(i)))
        result = add(result, term)
    return result


def audit(parent_path, child_path):
    old = json.loads(parent_path.read_text())
    new = json.loads(child_path.read_text())
    ni = {v['name']: i for i, v in enumerate(old['variables'])}
    get = lambda name: var(ni[name])
    f = get('crt.growth_majorant_F')
    radius = get('mul.1')
    t = add(get('t0'), const(16))
    x = get('x')
    y = get('y')
    b = get('choose0.output')
    q = get('pow2.output')
    bh = get('self_radix.BH')
    d = get('growth.power_base')
    h = get('cofinal.horizon_root')
    c_old = ni['crt.encoded_index_minus_one']
    beta_half = get('beta.odd_square_root_half')
    old_beta = get('beta.odd_square_multiplier')
    radix_half = get('radix.odd_square_root_half')

    old_reps = [add(get('crt.encoded.'+s), const(1))
                for s in ('a','b','c','d','S','Sp','u','vq')]
    old_reps.append(add(var(c_old), const(1)))
    reps = old_reps[:-1] + [scale(var(c_old), 2)]

    substitution = {
        ni['cofinal.horizon_root']: scale(h, 2),
        ni['mul.1']: f,
        c_old: add(scale(var(c_old), 2), const(-1)),
        ni['beta.odd_square_multiplier']: add(scale(beta_half, 2), const(1)),
    }
    delete_expected = {
        'radius': add(radius, scale(sq(f), -1)),
        'radix': add(q, scale(sq(add(scale(radix_half, 2), const(1))), -1)),
        'beta': add(old_beta, scale(sq(add(scale(beta_half, 2), const(1))), -1)),
    }
    deleted = []
    expected_rows = []
    edits = 0
    for i, row in enumerate(old['residuals']):
        p = poly(row['terms'])
        which = next((k for k, v in delete_expected.items() if p == v), None)
        if which is not None:
            deleted.append(which)
            continue
        if row['label'] == 'self_radix.base_definition':
            p = add(bh, scale(mul(b, add(const(2), scale(add(*old_reps), 4))), -1))
        elif row['label'] == 'growth.base_definition':
            p = add(d, scale(t, -1))
        p = substitute(p, substitution)
        edits += p != poly(row['terms'])
        expected_rows.append((row['label'], p))
    fail_unless(sorted(deleted) == ['beta', 'radius', 'radix'], 'unexpected deleted rows')
    fail_unless(len(expected_rows) == len(new['residuals']), 'row count mismatch')
    for i, ((label, expected), actual) in enumerate(zip(expected_rows, new['residuals'])):
        fail_unless(label == actual['label'], f'row label mismatch at {i}')
        fail_unless(expected == poly(actual['terms']), f'whole-row mismatch at {i}')
        fail_unless(max(map(len, expected), default=0) <= 2, f'nonquadratic row {i}')

    expected_variables = json.loads(json.dumps(old['variables']))
    expected_variables[c_old]['name'] = 'crt.even_index_half'
    expected_variables[ni['beta.odd_square_root_half']]['name'] = 'beta.odd_multiplier_half'
    fail_unless(new['variables'] == expected_variables, 'unexpected coordinate metadata')
    all_monomials = [m for row in new['residuals'] for m in poly(row['terms'])]
    for dead in ('mul.1', 'radix.odd_square_root_half', 'beta.odd_square_multiplier'):
        fail_unless(all(ni[dead] not in m for m in all_monomials), f'dead coordinate still used: {dead}')

    by_label = defaultdict(list)
    for row in new['residuals']:
        by_label[row['label']].append(poly(row['terms']))
    check_row = lambda label, p: fail_unless(by_label[label] == [p], f'bad semantic row: {label}')
    check_row('growth.base_definition', add(d, scale(t, -1)))
    check_row('cofinal.horizon', add(get('t0'), scale(sq(h), -4)))
    check_row('self_radix.base_definition', add(bh, scale(mul(b, add(const(2), scale(add(*reps), 4))), -1)))
    check_row('bootstrap.beta_base_square_product', add(y, scale(mul(f, add(scale(beta_half, 2), const(1))), -1)))
    check_row('crt.reciprocal_index_congruence', add(reps[-1], f, const(1), scale(get('mul.38'), -1)))
    gate = add(get('mul.38'), scale(mul(b, get('crt.index_quotient')), -1))
    fail_unless(any(poly(row['terms']) == gate for row in new['residuals']), 'index quotient multiplication missing')

    out = lambda k: f if k == 0 else get(f'pow{k}.output')
    requests = [
        (d, t, out(0)), (b, x, out(1)), (bh, x, out(2)),
        (add(q, const(1)), add(f, t), out(3)),
        (q, t, out(4)), (add(q, const(1)), reps[0], out(5)),
        (q, add(t, const(1)), out(6)),
        (add(q, const(1)), reps[1], out(7)),
        (add(q, const(1)), reps[2], out(8)),
        (add(q, const(1)), reps[3], out(9)),
        (add(q, const(1)), reps[4], out(10)),
        (q, add(y, const(1)), out(11)),
        (add(q, const(1)), reps[5], out(12)),
        (add(q, const(1)), reps[6], out(13)),
        (q, x, out(14)),
        (add(q, const(1)), reps[7], out(15)),
        (add(q, const(1)), reps[8], out(16)),
        (add(q, const(1)), add(get('add.380'), const(1)), out(17)),
    ]
    atoms = {tuple(sorted(p.items())): p for request in requests for p in request}
    frame = add(get('shared.W'), const(-2), *[scale(sq(p), -1) for p in atoms.values()])
    check_row('shared.frame_definition', frame)

    # The slot d is retained alongside t in the raw frame, although d=t is
    # an explicit source row. Retaining this duplicate square only strengthens
    # the old absolute bounds; no request atom is omitted.
    fail_unless(d != t and len(atoms) >= 1, 'expected retained affine growth slot')
    return {
        'status': 'PASS',
        'parent_sha256': hashlib.sha256(parent_path.read_bytes()).hexdigest(),
        'child_sha256': hashlib.sha256(child_path.read_bytes()).hexdigest(),
        'parent_rows': len(old['residuals']), 'child_rows': len(new['residuals']),
        'deleted_rows': deleted, 'changed_surviving_rows': edits,
        'whole_row_equalities': len(expected_rows), 'power_requests': len(requests),
        'raw_frame_atoms': len(atoms),
        'scope': 'Entire source mutation and complete square-frame atom coverage; ordinary semantic proof supplied separately',
    }


if __name__ == '__main__':
    if len(sys.argv) not in (3, 4):
        raise SystemExit(__doc__)
    result = audit(Path(sys.argv[1]), Path(sys.argv[2]))
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if len(sys.argv) == 4:
        Path(sys.argv[3]).write_text(text)
    print(text, end='')
