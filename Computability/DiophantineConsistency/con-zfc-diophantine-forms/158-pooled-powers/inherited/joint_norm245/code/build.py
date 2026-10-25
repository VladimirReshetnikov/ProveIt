#!/usr/bin/env python3
"""Compile a common signed ceiling and digit budget into a literal quartic.

This produces finite polynomial data. The unbounded mathematical equivalence
is proved in PROOF.md; these routines do not decide consistency or solvability.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / 'inherited' / 'normalized252'
sys.path.insert(0, str(PARENT / 'code'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T


def read(path):
    return json.loads(path.read_text())


def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(E.canonical_bytes(obj))


def sha(obj):
    return hashlib.sha256(E.canonical_bytes(obj)).hexdigest()


def change_source():
    original = read(PARENT / 'data' / 'guarded.json')
    old_transform = read(PARENT / 'data' / 'remainder_transformation.json')
    source = copy.deepcopy(original)
    names = {v['name']: i for i, v in enumerate(source['variables'])}
    f, b, v = [names[s] for s in ('fact0.output', 'choose0.output', 'pow0.output')]
    r, s = [names[x] for x in ('fact0.remainder', 'fact0.slack')]
    m = names['pow14.output']
    front = [g for g in old_transform['new_guards'] if g['kind'] == 'front_nonnegative']
    if len(front) != 3 or {g['coordinate'] for g in front} != {r, s, names['choose0.oslack']}:
        raise ValueError('Unexpected exact source front guards')
    removed = {g['row'] for g in front}
    product = names['mul.5']
    expected_product = E.normalize([[-1,[f,b]],[1,[product]]])
    row_edits = []
    for i, row in enumerate(source['residuals']):
        if row['label'] in ('fact0.ceiling', 'fact0.remainder_bound'):
            removed.add(i)
        if E.normalize(row['terms']) == expected_product:
            removed.add(i)
    if len(removed) != 6:
        raise ValueError('Expected three scalar guards and three ceiling rows')
    removed_rows = [{'row': i, 'content': original['residuals'][i]} for i in sorted(removed)]
    source['residuals'] = [row for i,row in enumerate(source['residuals']) if i not in removed]
    vp = len(source['variables'])
    sp = vp+1
    source['variables'] += [
        {'name':'ceiling.ratio', 'kind':'signed_witness'},
        {'name':'ceiling.normalized_slack', 'kind':'signed_witness'},
    ]
    additions = [
        {'label':'ceiling.common_ratio', 'terms':E.as_terms(E.normalize([[1,[m]],[-1,[b,vp]]]))},
        {'label':'ceiling.scaled_identity', 'terms':E.as_terms(E.normalize([[1,[f,m]],[-1,[vp,v]],[-1,[sp]]]))},
    ]
    source['residuals'] += additions
    budget_row = original['residuals'][old_transform['new_guards'][-1]['row']]
    if old_transform['new_guards'][-1]['kind'] != 'centered_remainder_budget':
        raise ValueError('Expected final normalized-remainder guard')
    count_budget = 0
    count_radix = 0
    reps = [names['crt.encoded.'+x] for x in ('a','b','c','d','S','Sp','u','vq')]
    reps += [names['crt.encoded_index_minus_one']]
    old_radix = E.normalize([[-10,[b]], *[[-1,[b,j]] for j in reps], [1,[522]]])
    new_radix = E.normalize([[-19,[b]], *[[-2,[b,j]] for j in reps], [1,[522]]])
    for i,row in enumerate(source['residuals']):
        if row == budget_row:
            changed = dict(row, terms=E.as_terms(F.add(E.normalize(row['terms']), {(sp,sp):-4})))
            source['residuals'][i] = changed
            row_edits.append({'kind':'add_normalized_ceiling_to_norm','old':row,'new':changed})
            count_budget += 1
        if row['label'] == 'self_radix.base_definition':
            if E.normalize(row['terms']) != old_radix:
                raise ValueError('Unexpected nine-representative radix base')
            changed = dict(row, terms=E.as_terms(new_radix))
            source['residuals'][i] = changed
            row_edits.append({'kind':'odd_nonzero_radix_multiplier','old':row,'new':changed})
            count_radix += 1
    if (count_budget,count_radix) != (1,1):
        raise ValueError('Expected one source edit of each kind')
    for row in source['residuals']:
        if E.degree(E.normalize(row['terms'])) > 2:
            raise ValueError('Degree exceeded two')
    source['variant'] += ':odd_multiplier_and_normalized_rounded_ceiling'
    cert = {
        'schema':'normalized_rounded_ceiling_v1',
        'parent_guarded_sha256':sha(original),
        'parent_remainder_transform_sha256':sha(old_transform),
        'removed_rows':removed_rows,
        'removed_guards':front,
        'row_edits':row_edits,
        'added_variables':[[vp,source['variables'][vp]],[sp,source['variables'][sp]]],
        'added_rows':additions,
        'semantic_coordinates':{'F':f,'B':b,'V':v,'M':m,'vB':vp,'S':sp,'old_r':r,'old_s':s,'base_BH':522},
        'representatives':[{'stored':j,'actual_shift':1} for j in reps],
        'source_sha256':sha(source),
    }
    return source,cert


def build(output, cap=16):
    source,cert = change_source()
    factored,fc = F.transform(source)
    projected,pc,_ = E.optimize(factored,max_support=cap)
    replay = E.verify(factored,projected,pc)
    shifts = {i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'].endswith('minus1')}
    shifts.update({i:-16 for i,v in enumerate(projected['variables']) if v['name']=='t0'})
    final = T.translate(projected,shifts)
    poly = E.expand(final)
    metrics = {
        'variables':len(final['variables']),
        'rows':len(final['residuals']),
        'degree':max(len(m) for c,m in poly['terms']),
        'monomials':len(poly['terms']),
        'height':max(abs(c) for c,m in poly['terms']),
        'row_height':max(abs(c) for row in final['residuals'] for c,m in row['terms']),
        'domain':'unrestricted integers',
    }
    trans = {
        'schema':'integral_translation_v1',
        'input_sha256':sha(projected),'output_sha256':sha(final),
        'shifts':[[i,s] for i,s in shifts.items()],
        'convention':'old=new+shift',
    }
    outputs = [
        ('source.json',source),('source_transformation.json',cert),
        ('factored_source.json',factored),('factorization_certificate.json',fc),
        ('projected.json',projected),('projection_certificate.json',pc),
        ('PROJECTION_CHECK.json',replay),('translation_certificate.json',trans),
        ('equation.json',final),('expanded_polynomial.json',poly),('METRICS.json',metrics),
    ]
    for name,obj in outputs:
        write(output/name,obj)
    return metrics


if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'data')
    ap.add_argument('--cap',type=int,default=16)
    args=ap.parse_args()
    print(json.dumps(build(args.output,args.cap),indent=2))
