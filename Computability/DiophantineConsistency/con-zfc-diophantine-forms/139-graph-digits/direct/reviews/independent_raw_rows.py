"""Independent literal check of selected four-pool/fused-cap transformations.

This script does not import the producer or its transformation certificate.
It reconstructs the changes using original named rows and coordinates.
It does not prove the inherited arithmetic/calculus calibration.
"""
from collections import Counter
from copy import deepcopy
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
def read(path): return json.loads(path.read_text())
def poly(terms):
    out={}
    for c,m in terms:
        m=tuple(sorted(m)); out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def key(row):return (row['label'],tuple(sorted(poly(row['terms']).items())))
def verify(parent,target):
    pn={v['name']:i for i,v in enumerate(parent['variables'])}
    renamed={
        'pooled_digits.t0.slack':'choose0.modular_rslack',
        'pooled_digits.t.slack':'crt.range.a.modular_rslack',
        'pooled_digits.y.slack':'crt.range.S.modular_rslack',
        'pooled_digits.x.slack':'crt.range.u.modular_rslack',
        'index_cap.fused_quotient':'index_cap.error_square_quotient',
    }
    remap={i:pn[renamed.get(v['name'],v['name'])] for i,v in enumerate(target['variables'])}
    if len(set(remap.values())) != len(remap):raise ValueError('coordinate alias')
    actual=[]
    for row in target['residuals']:
        actual.append({'label':row['label'],'terms':[[c,[remap[i] for i in m]] for c,m in row['terms']]})
    by_label={r['label']:r for r in parent['residuals'] if r['label']!='addition'}
    groups=[('t0',['choose0','crt.range.index']),
            ('t',['crt.range.'+x for x in ('a','b','c','d','derived_label_sum')]),
            ('y',['crt.range.S','crt.range.Sp']),
            ('x',['crt.range.u','crt.range.vq'])]
    old_bounds={p+'.remainder_bound' for _,members in groups for p in members}
    cap_chain={pn[x] for x in ('index_cap.aggregate_slack','add.589','add.593','add.597','add.601')}
    removed_cap=[r for r in parent['residuals'] if any(i in cap_chain for c,m in r['terms'] for i in m)]
    if len(removed_cap)!=5:raise ValueError('cap closure changed')
    expected=[deepcopy(r) for r in parent['residuals'] if r['label'] not in old_bounds and r not in removed_cap and r['label']!='index_cap.squared_index_errors']
    for label,members in groups:
        first=deepcopy(by_label[members[0]+'.remainder_bound'])
        denominator=[m[0] for c,m in first['terms'] if c==1 and len(m)==1]
        if len(denominator)!=1:raise ValueError('denominator layout')
        for name in members[1:]:
            other=by_label[name+'.remainder_bound']
            den=[m[0] for c,m in other['terms'] if c==1 and len(m)==1]
            if den!=denominator:raise ValueError('pooled distinct denominators')
            first['terms'].append([-1,[pn[name+'.modular_remainder']]])
        first['label']='pooled_digits.'+label
        expected.append(first)
    # Reconstruct H independently from add.589 = H+1+aggregate_slack.
    slack=pn['index_cap.aggregate_slack']; initial=pn['add.589']
    cap_initial=[r for r in removed_cap if any(initial in m for c,m in r['terms']) and any(slack in m for c,m in r['terms'])]
    if len(cap_initial)!=1:raise ValueError('initial cap row')
    H=[[-c,m] for c,m in cap_initial[0]['terms'] if m not in ([slack],[initial])]
    H.append([-1,[]])
    quotient=pn['index_cap.error_square_quotient']
    fused=deepcopy(by_label['index_cap.squared_index_errors'])
    fused['terms']=[[-c if quotient in m else c,m] for c,m in fused['terms']]
    fused['terms']+=H+[[-1,[pn['index_cap.Y']]]]
    fused['label']='index_cap.fused_bound_errors'
    expected.append(fused)
    if Counter(map(key,actual)) != Counter(map(key,expected)):
        raise ValueError('literal changed/unchanged row mismatch')
    if 'choose0.digit_bound' not in {r['label'] for r in actual}:
        raise ValueError('factorial digit bound was removed')
    if len(target['variables'])!=332 or len(target['residuals'])!=281:
        raise ValueError('wrong selected source dimensions')
    return {'variables':332,'rows':281,'unchanged_rows':len(expected)-5,'pooled_rows':4,'fused_rows':1,'factorial_digit_bound_retained':True}

if __name__=='__main__':
    parent=read(ROOT/'upstream/129-semantic-pell-anchor/equations/source/equation.json')
    receipt={}
    for endpoint in ('common_source',):
        target=read(ROOT/'equations/source/equation.json')
        receipt[endpoint]=verify(parent,target)
    target=read(ROOT/'equations/source/equation.json')
    rejected=[]
    for label in ('pooled_digits.t0','pooled_digits.t','index_cap.fused_bound_errors'):
        bad=deepcopy(target)
        row=next(r for r in bad['residuals'] if r['label']==label)
        row['terms'].append([1,[]])
        try: verify(parent,bad)
        except ValueError:rejected.append(label)
        else:raise ValueError('mutation accepted')
    receipt['rejected_constant_mutations']=rejected
    receipt['scope']='Exact raw-row binding only; unbounded claims reviewed separately; no inherited calibration audit.'
    print(json.dumps(receipt,indent=2))
