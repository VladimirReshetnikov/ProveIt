#!/usr/bin/env python3
"""Compose the full common-remainder quartic with an odd-square radix.

Only the published final parent is transformed.  Its private output-slack
ternary guard is replaced by q=(2z+1)^2.  The semantic proof is in PROOF.md;
this program constructs the exact finite polynomial, not a consistency test.
"""
from pathlib import Path
import argparse, copy, hashlib, json
from collections import defaultdict

ROOT=Path(__file__).resolve().parent

def canonical(x):
    return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()

def expand(e):
    p=defaultdict(int)
    for r in e['residuals']:
        for c,m in r['terms']:
            for d,n in r['terms']:
                p[tuple(sorted(m+n))]+=c*d
    return [[c,list(m)] for m,c in sorted(p.items()) if c]

def produce():
    path=ROOT/'parent252/equation/equation.json'
    parent=json.loads(path.read_text())
    tr=json.loads((path.parent/'translation_certificate.json').read_text())
    names={v['name']:i for i,v in enumerate(parent['variables'])}
    q=names['pow2.output'];B=names['choose0.output']
    qshift=dict(tr['shifts']).get(q,0)
    if qshift!=-1 or dict(tr['shifts']).get(B,0)!=0:
        raise ValueError('Unexpected inherited translations')
    deleted=[names['new_guard2.'+c] for c in 'abc']
    matches=[i for i,r in enumerate(parent['residuals']) if r['label']=='domain_guard.2']
    if len(matches)!=1: raise ValueError('Missing unique output guard')
    guardrow=matches[0]; a,b,c=deleted
    expected=sorted([[-2,[]],[-1,[B]],[1,[q]],[-1,[a,a]],[-1,[b,b]],[-1,[c]],[-1,[c,c]]],key=lambda t:t[1])
    if parent['residuals'][guardrow]['terms']!=expected:
        raise ValueError('Parent output guard differs')
    for i,r in enumerate(parent['residuals']):
        if i!=guardrow and any(j in m for _,m in r['terms'] for j in deleted):
            raise ValueError('Deleted witness is not private')
    keep=[i for i in range(len(parent['variables'])) if i not in deleted]
    ren={i:j for j,i in enumerate(keep)}
    result=copy.deepcopy(parent)
    result['variables']=[copy.deepcopy(parent['variables'][i]) for i in keep]
    z=len(keep)
    result['variables'].append({'kind':'integer_witness','name':'radix.odd_square_root_half'})
    rows=[]
    for i,r in enumerate(parent['residuals']):
        if i==guardrow: continue
        rows.append({'label':r['label'],'terms':[[c,[ren[j] for j in m]] for c,m in r['terms']]})
    rows.append({'label':'radix.odd_square','terms':[[-2,[]],[1,[ren[q]]],[-4,[z]],[-4,[z,z]]]})
    result['residuals']=rows
    result['variant']='normalized_common_remainders_odd_square_250'
    result.pop('wire_eliminated_source_sha256',None)
    result['parent_equation_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
    terms=expand(result)
    poly={'schema':'sparse_integer_polynomial_v1','domain':'Z','variable_count':len(result['variables']),'terms':terms}
    metrics={'variables':len(result['variables']),'rows':len(rows),'degree':max(len(m) for c,m in terms),'monomials':len(terms),'height':max(abs(c) for c,m in terms),'row_height':max(abs(c) for r in rows for c,m in r['terms'])}
    cert={'schema':'odd_square_composition_v1','parent_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'removed_row':guardrow,'removed_variables':deleted,'kept_parent_coordinates':keep,'new_coordinate':z,'q_parent_coordinate':q,'q_parent_shift':qshift,'B_parent_coordinate':B,'semantics':'actual q = parent[q] - 1; every retained coordinate is unchanged'}
    return {'equation.json':result,'expanded_polynomial.json':poly,'METRICS.json':metrics,'transformation.json':cert}

def main():
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    out=ROOT/'equation250';out.mkdir(exist_ok=True)
    data=produce()
    for name,value in data.items():
        raw=canonical(value);path=out/name
        if a.check:
            if path.read_bytes()!=raw:raise ValueError('Rebuild differs: '+name)
        else:path.write_bytes(raw)
    print(json.dumps(data['METRICS.json'],sort_keys=True))

if __name__=='__main__':main()
