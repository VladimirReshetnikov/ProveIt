#!/usr/bin/env python3
"""Independent finite audit; imports no producer modules."""
from pathlib import Path
from collections import Counter
import json, copy, itertools, argparse
cli = argparse.ArgumentParser(description=__doc__)
cli.add_argument('--source-dir', type=Path, default=Path(__file__).resolve().parents[1] / 'data')
cli.add_argument('--endpoint-dir', type=Path, default=Path(__file__).resolve().parents[1] / 'equation')
a = cli.parse_args()
BASE = a.source_dir
END = a.endpoint_dir

def check(condition, message='Independent verification failed'):
    if not condition:
        raise ValueError(message)

def read(n, b=BASE):
    return json.loads((b / (n + '.json')).read_text())

def poly(t):
    return {tuple(sorted(m)): c for c, m in t if c}

def add(*ps):
    d = Counter()
    for p in ps:
        for m, c in p.items():
            d[m] += c
    return {m: c for m, c in d.items() if c}

def smul(p, k):
    return {m: c * k for m, c in p.items() if c * k}

def mul(p, q):
    d = Counter()
    for m, c in p.items():
        for n, e in q.items():
            d[tuple(sorted(m + n))] += c * e
    return {m: c for m, c in d.items() if c}

def sub(p, x, q):
    d = {}
    for m, c in p.items():
        t = {(): c}
        for j in m:
            t = mul(t, q if j == x else {(j,): 1})
        d = add(d, t)
    return d
v = lambda i: {(i,): 1}
terms = lambda p: [[c, list(m)] for m, c in sorted(p.items())]
old = read('parent_source')
pc = read('parent_transform_certificate')
new = read('source')
tf = read('remainder_transformation')
intervals = [g for g in pc['guards'] if g['kind'] == 'postsemantic_interval']
names = {x['name']: i for i, x in enumerate(old['variables'])}
M = names['pow14.output']
N = names['pow1.output']
groups = {}
bound = set()
for g in intervals:
    r, s = g['pair']
    bp = poly(old['residuals'][g['bound_row']]['terms'])
    L = add(bp, v(r), v(s), {(): 1})
    check(len(L) == 1)
    (mon, c), = L.items()
    check(len(mon) == 1 and c == 1)
    check(poly(g['expression']) == mul(v(r), v(s)))
    groups.setdefault(mon[0], []).append(r)
    bound.add(g['bound_row'])
check(len(intervals) == 11 and sorted(map(len, groups.values())) == [2, 2, 2, 5])
rows = [copy.deepcopy(r) for i, r in enumerate(old['residuals']) if i not in bound]
variables = copy.deepcopy(old['variables'])
ratios = {}
for j, (L, rems) in enumerate(sorted(groups.items())):
    if L == M:
        continue
    q = len(variables)
    ratios[L] = q
    variables.append({'name': f'remainder_budget.ratio{j}', 'kind': 'signed_witness'})
    rows.append({'label': f'remainder_budget.ratio{j}', 'terms': terms(add(v(M), smul(mul(v(L), v(q)), -1)))})

def product_wire(a, b):
    target = mul(v(a), v(b))
    hits = []
    for ri, rr in enumerate(rows):
        pp = poly(rr['terms'])
        for mon, c in pp.items():
            if len(mon) == 1 and c == 1 and (add(pp, smul(v(mon[0]), -1)) == smul(target, -1)):
                hits.append((ri, mon[0]))
    check(len(hits) == 1)
    return hits[0]
_, common = product_wire(N, M)
aliases = {}
drop = set()
for L in groups:
    if L != M:
        ri, z = product_wire(N, L)
        drop.add(ri)
        aliases[z] = common
for L, rems in groups.items():
    for r in rems:
        hits = [(i, rr) for i, rr in enumerate(rows) if any((r in mon for mon in poly(rr['terms'])))]
        check(len(hits) == 1)
        ri, rr = hits[0]
        pp = poly(rr['terms'])
        check(pp[r,] == -1)
        us = [mon[0] for mon, c in pp.items() if len(mon) == 1 and c == 1 and variables[mon[0]]['name'].startswith('pow')]
        check(len(us) == 1)
        u = us[0]
        check(len(pp) == 3)
        if L != M:
            rows[ri] = dict(rr, terms=terms(add(pp, smul(v(u), -1), mul(v(u), v(ratios[L])))))
        variables[r]['name'] = 'normalized.' + variables[r]['name']
        if rr['label'] == 'choose0.digit':
            z = next((mon[0] for mon, c in pp.items() if c == -1 and len(mon) == 1 and (mon[0] != r)))
            hits = [i for i, dr in enumerate(rows) if dr['label'] == 'multiplication' and poly(dr['terms']).get((z,)) == 1]
            check(len(hits) == 1)
            i = hits[0]
            dp = poly(rows[i]['terms'])
            check(all((L in mon for mon in dp if mon != (z,))))
            rows[i] = dict(rows[i], terms=terms(sub(dp, L, v(M))))
result = []
for i, rr in enumerate(rows):
    if i in drop:
        continue
    pp = poly(rr['terms'])
    for x, y in aliases.items():
        pp = sub(pp, x, v(y))
    result.append(dict(rr, terms=terms(pp)))
# Independently reconstruct the new centered-ceiling and odd-square rows.
ceiling_rows=[r for r in result if r['label'] in ('fact0.ceiling','fact0.remainder_bound')]
check(len(ceiling_rows)==2, 'two old ceiling rows')
for rr in result:
    if rr['label'] not in ('fact0.ceiling','fact0.remainder_bound'):
        check(not any(names[n] in m for n in ('fact0.remainder','fact0.slack') for c,m in rr['terms']), 'private ceiling escape')
result=[r for r in result if r['label'] not in ('fact0.ceiling','fact0.remainder_bound')]
vB=len(variables);S=vB+1;z=vB+2
variables += [{'name':'remainder_budget.'+n,'kind':'signed_witness'} for n in ('ceiling_ratio','ceiling_residue','odd_radix_root')]
result += [
 {'label':'remainder_budget.ceiling_ratio','terms':terms(add(v(M),smul(mul(v(names['choose0.output']),v(vB)),-1)))},
 {'label':'remainder_budget.ceiling_scaled','terms':terms(add(mul(v(vB),v(names['pow0.output'])),v(S),smul(mul(v(M),v(names['fact0.output'])),-1)))},
 {'label':'remainder_budget.odd_radix_square','terms':terms(add(v(names['pow2.output']),{(z,z):-4,(z,):-4,():-1}))}
]
check(variables == new['variables'], 'complete new variable list')
check(result == new['residuals'], 'complete new source rows')

rems = [r for rs in groups.values() for r in rs]
front=[g for g in pc['guards'] if g['kind']=='front_nonnegative']
check(len(front)==3 and {g['coordinate'] for g in front}=={names['fact0.remainder'],names['fact0.slack'],names['choose0.oslack']},'exact three removed front guards')
guards = [g for g in pc['guards'] if g['kind'] not in ('postsemantic_interval','front_nonnegative')]
check(len(guards)==1 and guards[0]['kind']=='shared_square_cap','only inherited anchor guard remains')
budget = add(mul(v(M), v(M)), {(): -1}, smul(add(*[mul(v(r), v(r)) for r in rems],mul(v(S),v(S))), -4))
guards.append({'kind': 'centered_remainder_budget', 'expression': terms(budget)})
expected = copy.deepcopy(new)
expected['variant'] += ':shared_centered_remainders'
for j, g in enumerate(guards):
    a = len(expected['variables'])
    b, c = (a + 1, a + 2)
    expected['variables'] += [{'name': f'new_guard{j}.{s}', 'kind': 'integer_guard'} for s in ('a', 'b', 'c')]
    pp = add(poly(g['expression']), {(a, a): -1, (b, b): -1, (c, c): -1, (c,): -1})
    expected['residuals'].append({'label': f'domain_guard.{j}', 'terms': terms(pp)})
check(expected == read('guarded'))
f = read('factored_source')
import inherited_independent_algebra as IA
factorization_edits = IA.factorization(read('guarded'), f, read('factorization_certificate'))
pr = read('projection_certificate')
polys = {i: poly(r['terms']) for i, r in enumerate(f['residuals'])}
for st in pr['steps']:
    i, x = (st['row_id'], st['variable'])
    q = poly(st['restoration'])
    check(all((x not in m for m in q)))
    expected = add(v(x), smul(q, -1))
    check(polys[i] in (expected, smul(expected, -1)))
    del polys[i]
    for j in list(polys):
        if any((x in m for m in polys[j])):
            polys[j] = sub(polys[j], x, q)
        check(max(map(len, polys[j]), default=0) <= 2)
check(sorted(polys) == pr['retained_original_rows'])
keep = pr['retained_original_variables']
reindex = {x: i for i, x in enumerate(keep)}
actual = read('projected')
check(actual['variables'] == [f['variables'][i] for i in keep])
check(len(actual['residuals']) == len(polys))
for oldi, rr in zip(sorted(polys), actual['residuals']):
    p = {tuple(sorted((reindex[x] for x in m))): c for m, c in polys[oldi].items()}
    check(poly(rr['terms']) == p)
for x in pr['unconstrained_removed']:
    check(not any((x in m for p in polys.values() for m in p)))
eq = read('equation', END)
expanded = read('expanded_polynomial', END)
tr = read('translation_certificate', END)
check(tr['convention'] == 'old=new+shift')
check(len(eq['residuals']) == len(actual['residuals']))
for oldrow, newrow in zip(actual['residuals'], eq['residuals']):
    pp = poly(oldrow['terms'])
    for i, shift in tr['shifts']:
        pp = sub(pp, i, add(v(i), {(): shift}))
    check(pp == poly(newrow['terms']))
ss = {}
for rr in eq['residuals']:
    p = poly(rr['terms'])
    check(max(map(len, p), default=0) <= 2)
    ss = add(ss, mul(p, p))
check(ss == poly(expanded['terms']))
used = {i for m in ss for i in m}
check(used == set(range(len(eq['variables']))))
metrics = {'variables': len(eq['variables']), 'rows': len(eq['residuals']), 'degree': max(map(len, ss)), 'monomials': len(ss), 'height': max(map(abs, ss.values()))}
check(metrics == {k: read('METRICS', END)[k] for k in metrics})
print(json.dumps({'status': 'PASS', 'independent_source_reconstruction': True, 'independent_guard_reconstruction': True, 'independent_monic_steps': len(pr['steps']), 'independent_horn_factorization_edits': factorization_edits, 'independent_sos_collection': True, 'independent_final_translation': True, 'metrics': metrics, 'scope': 'No producer modules imported. The inherited independent checker verifies every Horn factoring edit; all source edits, sign guards, monic projections, final translation, and the final SOS collection are independently replayed.'}, indent=2))
