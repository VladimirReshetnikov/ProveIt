#!/usr/bin/env python3
"""Independent finite audit of deferred guards and the typed Pell budget.

Only Python's standard library is imported. The unbounded arithmetic proof
is in INDEPENDENT_MATHEMATICAL_REVIEW.md; finite sweeps are diagnostics.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path


def need(ok, message):
    if not ok:
        raise ValueError(message)


def poly(terms):
    d = defaultdict(int)
    for coefficient, monomial in terms:
        d[tuple(sorted(monomial))] += coefficient
    return {m: c for m, c in d.items() if c}


def plus(a, b):
    d = defaultdict(int, a)
    for m, c in b.items():
        d[m] += c
    return {m: c for m, c in d.items() if c}


def scale(a, c):
    return {m: c*v for m, v in a.items() if c*v}


def times(a, b):
    d = defaultdict(int)
    for m, c in a.items():
        for n, e in b.items():
            d[tuple(sorted(m+n))] += c*e
    return {m: c for m, c in d.items() if c}


def rename(p, mapping):
    d = defaultdict(int)
    for m, c in p.items():
        d[tuple(sorted(mapping[v] for v in m))] += c
    return {m: c for m, c in d.items() if c}


def load(path):
    return json.loads(path.read_text())


def run(folder):
    old = load(folder/'source/parent.json')
    src = load(folder/'fused_source.json')
    fuse = load(folder/'fusion_certificate.json')
    cert = load(folder/'budget_certificate.json')
    oldnames = {v['name']:i for i,v in enumerate(old['variables'])}
    names = {v['name']:i for i,v in enumerate(src['variables'])}
    mp = {oldid:newid for newid,oldid in enumerate(fuse['retained_before_reindex'])}
    deleted = set(fuse['deleted_rows'])
    deleted_variables = set(fuse['deleted_private_witnesses'])
    removed_guard_coordinates = set(map(int, fuse['old_guard_rows']))
    reconstructed = []
    f = fuse['factorial_guard']['source_coordinate']
    need(f == oldnames['fact0.output'], 'Wrong factorial coordinate')
    for ri, row in enumerate(old['residuals']):
        if ri in deleted:
            need(row['label'].startswith('nonnegative.'), 'Deleted a non-guard row')
            guarded = int(row['label'].split('.')[1])
            need(guarded in removed_guard_coordinates, 'Unlisted guard deletion')
            a,b,c = (oldnames[f'nonnegative.{guarded}.{s}'] for s in 'abc')
            expected = {(guarded,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
            need(poly(row['terms']) == expected, 'Wrong old guard polynomial')
            continue
        p = poly(row['terms'])
        need(not deleted_variables.intersection(v for m in p for v in m),
             'Deleted private witness escapes its guard')
        if row['label'] == f'nonnegative.{f}':
            p = plus(p, {():-1})
        if row['label'] == 'shared.frame_definition':
            p = poly(cert['new_frame']['terms'])
        else:
            p = rename(p, mp)
        reconstructed.append((row['label'],p))
    for record in fuse['new_guards_before_reindex']:
        if 'square_row' in record:
            row = record['square_row']
            reconstructed.append((row['label'], rename(poly(row['terms']),mp)))
        row = record['row']
        reconstructed.append((row['label'], rename(poly(row['terms']),mp)))
    actual = [(r['label'],poly(r['terms'])) for r in src['residuals']]
    need(reconstructed == actual, 'Full source transformation mismatch')
    need(fuse['joint_anchor'], 'This reviewed variant requires the joint guard')
    anchor = fuse['new_guards_before_reindex'][-1]
    A,v,u = anchor['A'],anchor['v'],anchor['square_variable']
    need(A == oldnames['shared.A'], 'Wrong frame base')
    need(v == oldnames['shared_index.Vquotient_minus1'], 'Wrong common multiplier')
    need(poly(anchor['square_row']['terms']) ==
         {(u,):1,(v,v):-1,(v,):-2,():-1}, 'Incorrect multiplier square')
    a,b,c = anchor['auxiliary']
    expected = {tuple(sorted((A,u))):1,(u,):-1,():-1,
                (a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
    need(poly(anchor['row']['terms']) == expected, 'Incorrect joint guard')

    known = set(cert['initial_nonnegative'])
    guardnames = {r['label'] for r in src['residuals']}
    need(not known.intersection(removed_guard_coordinates), 'Deleted sign premise used')
    for x in known:
        need(f'nonnegative.{x}' in guardnames, 'Missing retained scalar guard')
    for st in cert['proof_steps']:
        x = st['variable']
        row = src['residuals'][st['row']]
        label = row['label']
        need(label != 'shared.frame_definition', 'Circular frame premise')
        need(not label.startswith(('nonnegative.','product_guard.','frame_orientation')),
             'Sign guard used as a monic source definition')
        rhs = poly(st['rhs'])
        need(all(c >= 0 for c in rhs.values()), 'Negative monomial coefficient')
        need(x not in {v for m in rhs for v in m}, 'Circular monic definition')
        expected = plus({(x,):1},scale(rhs,-1))
        need(poly(row['terms']) in (expected,scale(expected,-1)),
             'Source row is not the claimed monic definition')
        dependencies = {v for m in rhs for v,k in Counter(m).items() if k % 2}
        need(dependencies == set(st['dependencies']), 'Wrong odd-exponent dependency set')
        need(dependencies <= known, 'Unproved sign premise')
        known.add(x)
    total = {():2}
    linear = 0
    for atom in cert['atoms']:
        p = poly(atom['atom']['affine'])
        need(max(map(len,p),default=0) <= 1, 'Atom is not affine')
        if atom['nonnegative']:
            need(all(c >= 0 for c in p.values()), 'Signed coefficient in linear atom')
            need({v for m in p for v in m} <= known, 'Unproved linear atom sign')
            contribution = p
            linear += 1
        else:
            contribution = times(p,p)
        need(poly(atom['contribution']) == contribution, 'Wrong atom contribution')
        total = plus(total,contribution)
    W = names['shared.W']
    expected = plus({(W,):1},scale(total,-1))
    need(expected == poly(cert['new_frame']['terms']), 'Wrong collected frame')
    need(expected == poly(src['residuals'][cert['frame_row']]['terms']),
         'Certificate frame differs from actual source')

    # Boundary diagnostics supplement, but do not prove, the general lemmas.
    factorial_cases = pair_cases = joint_cases = 0
    for F in range(1,13):
        for r in range(-20,21):
            for s in range(-20,21):
                V = F*r+(F-1)*s+F
                if r*s >= 0 and V > F:
                    need(r >= 0 and s >= 0, 'Factorial-pair counterexample')
                    factorial_cases += 1
    for x in range(-40,41):
        for y in range(-40,41):
            if x+y > 0 and x*y >= 0:
                need(x >= 0 and y >= 0, 'Positive-sum pair counterexample')
                pair_cases += 1
    for A in range(-40,41):
        for v in range(-40,41):
            predicate = (A-1)*(v+1)**2-1 >= 0
            need(predicate == (A >= 2 and v != -1), 'Joint-guard counterexample')
            joint_cases += 1
    return {
        'status':'PASS',
        'source_sha256':hashlib.sha256((folder/'source/parent.json').read_bytes()).hexdigest(),
        'fused_source_sha256':hashlib.sha256((folder/'fused_source.json').read_bytes()).hexdigest(),
        'full_transformation_rows':len(actual),
        'pair_guards':fuse['pair_count'],
        'coupled_anchor_identity':True,
        'retained_scalar_sign_seeds':len(cert['initial_nonnegative']),
        'ordered_sign_steps':len(cert['proof_steps']),
        'budget_atoms':len(cert['atoms']),
        'linear_atoms':linear,
        'squared_atoms':len(cert['atoms'])-linear,
        'factorial_boundary_cases':factorial_cases,
        'pair_boundary_cases':pair_cases,
        'joint_boundary_assignments':joint_cases,
        'imports':'Python standard library only; no producer or optimizer imported',
        'scope':'Local finite application checks; see separate unbounded mathematical proof'
    }


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('folder',type=Path)
    ap.add_argument('--output',type=Path)
    args = ap.parse_args()
    receipt = run(args.folder)
    text = json.dumps(receipt,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')
