#!/usr/bin/env python3
"""Independent literal checker; imports no builder or upstream checker.

Checks original quadratic rows -> natural affine projection -> nonnegative
monic contraction -> every expanded coefficient.  All arithmetic is exact.
This is a finite certificate checker, not a proof of the logical calibration.
"""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import argparse, copy, hashlib, json

def need(condition,message):
    if not condition:
        raise ValueError(message)

def add(*items):
    d=Counter()
    for a in items:
        for m,c in a.items():
            d[m]+=c
    return {m:c for m,c in d.items() if c}

def scale(a,c):
    return {m:v*c for m,v in a.items() if v*c}

def mul(a,b):
    d=Counter()
    for m,c in a.items():
        for n,e in b.items():
            d[tuple(sorted(m+n))]+=c*e
    return {m:c for m,c in d.items() if c}

def decode(terms,rational=False):
    d={}
    for c,m in terms:
        m=tuple(m)
        need(tuple(sorted(m))==m,'unsorted monomial')
        need(m not in d,'duplicate monomial')
        d[m]=Fraction(*c) if rational else c
        need(d[m]!=0,'zero coefficient stored')
    return d

def var(v):
    return {(v,):1}

def replace(a,env):
    result={}
    for m,c in a.items():
        term={():c}
        for v in m:
            term=mul(term,env.get(v,var(v)))
        result=add(result,term)
    return result

def expand(rows):
    return add(*(mul(r,r) for r in rows))

def rowdict(row):
    return decode(row['terms'])

def read(path):
    return json.loads(path.read_text())

def verify_affine(meta,raw):
    names=[v['name'] for v in meta['variables']]
    targetnames=[v['name'] for v in raw['variables']]
    need(len(set(names))==len(names),'source names not unique')
    need(len(set(targetnames))==len(targetnames),'target names not unique')
    old={n:i for i,n in enumerate(names)}
    retained={old[n]:i for i,n in enumerate(targetnames)}
    gates={int(k):int(v) for k,v in meta['gates'].items()}
    env={k:var(v) for k,v in retained.items()}
    restored=[]
    for i in range(len(names)):
        if i in retained:
            continue
        need(i in gates,'missing nongate variable')
        r=rowdict(meta['rows'][gates[i]])
        need(r.get((i,))==1,'nonmonic raw gate')
        need(all(i not in m for m in r if m!=(i,)),'raw gate self-reference')
        rep=scale({m:c for m,c in r.items() if m!=(i,)},-1)
        need(all(v<i for m in rep for v in m),'gate not triangular')
        need(all(v in env for m in rep for v in m),'unrestored raw dependency')
        rep=replace(rep,env)
        need(all(c>=0 for c in rep.values()),'raw restoration lacks a positive-coefficient proof')
        env[i]=rep
        restored.append(i)
    actual=[]
    for r in meta['rows']:
        p=replace(rowdict(r),env)
        if p:
            actual.append((r['label'],p))
    expected=[(r['label'],rowdict(r)) for r in raw['residuals']]
    need(actual==expected,'full original-to-raw row identity failed')
    return {'all_original_rows':len(meta['rows']),'nonnegative_gate_restorations':len(restored),
        'retained_variables':len(retained),'remaining_rows':len(actual)}

def verify_contraction(raw,target,cert):
    rows={i:rowdict(r) for i,r in enumerate(raw['residuals'])}
    eliminated=[]
    for s in cert['steps']:
        v=s['variable_original_index'];rid=s['source_row_id'];sign=s['pivot_sign']
        need(v not in eliminated,'variable eliminated twice')
        need(sign in (-1,1),'nonunit pivot')
        need(rid in rows,'missing pivot row')
        restoration=decode(s['restoration'])
        need(all(v not in m for m in restoration),'self-referential restoration')
        need(rows[rid]==decode(s['row_before']),'recorded pivot row does not match')
        need(rows[rid]==scale(add(var(v),scale(restoration,-1)),sign),'pivot identity failed')
        nc=s['nonnegative_certificate']
        remainder=decode(nc['nonnegative_remainder'])
        need(all(c>=0 for c in remainder.values()),'negative certified remainder')
        proof=remainder
        for sq in nc['squares']:
            weight=Fraction(*sq['weight'])
            need(weight>=0,'negative square weight')
            form=decode(sq['affine_form'],True)
            need(all(len(m)<=1 for m in form),'non-affine certified square')
            proof=add(proof,scale(mul(form,form),weight))
        need(proof==restoration,'nonnegativity identity failed')
        del rows[rid]
        rows={i:replace(r,{v:restoration}) for i,r in rows.items()}
        eliminated.append(v)
    retained=cert['retained_original_indices_in_target_order']
    unused=cert['unused_original_indices_restored_to_zero']
    need(len(set(retained))==len(retained),'duplicate retained variable')
    need(set(retained).isdisjoint(eliminated),'retained eliminated variable')
    need(set(retained).isdisjoint(unused),'retained unused variable')
    need(set(eliminated).isdisjoint(unused),'eliminated unused variable')
    need(set(retained)|set(eliminated)|set(unused)==set(range(len(raw['variables']))),'incomplete variable partition')
    need(all(v not in set(unused) for row in rows.values() for monomial in row for v in monomial),
         'supposedly unused variable still occurs in a surviving row')
    env={v:var(i) for i,v in enumerate(retained)}|{v:{} for v in unused}
    ids=cert['surviving_source_row_ids_in_target_order']
    zeros=cert['zero_source_row_ids']
    need(set(ids)|set(zeros)==set(rows),'incomplete row partition')
    need(set(ids).isdisjoint(zeros),'overlapping row partition')
    need(all(not rows[i] for i in zeros),'nonzero discarded row')
    got=[replace(rows[i],env) for i in ids]
    want=[rowdict(r) for r in target['residuals']]
    need(got==want,'full contracted row identity failed')
    need([raw['variables'][v] for v in retained]==target['variables'],'target variable map failed')
    need(all(len(m)<=2 for r in got for m in r),'contracted row degree exceeds two')
    return {'monic_nonnegative_eliminations':len(eliminated),'retained_variables':len(retained),'rows':len(got)}

def verify_expansion(eq,poly):
    rows=[rowdict(r) for r in eq['residuals']]
    got=expand(rows)
    need(got==decode(poly['terms']),'collected polynomial differs')
    n=len(eq['variables'])
    need(poly['variables']==n,'polynomial variable count differs')
    need({v for m in got for v in m}==set(range(n)),'missing or out-of-range polynomial variable')
    return {'variables':n,'rows':len(rows),'degree':max(map(len,got)),'monomials':len(got),
        'coefficient_height':max(abs(v) for v in got.values())}

def check(directory,parent_directory=None):
    d=Path(directory)
    raw=read(d/'raw/equation.json');target=read(d/'natural/equation.json')
    meta=read(d/'raw/raw_audit_input.json')
    cert=read(d/'natural/elimination_certificate.json')
    receipt={'affine_projection':verify_affine(meta,raw),
        'contraction':verify_contraction(raw,target,cert),
        'raw_polynomial':verify_expansion(raw,read(d/'raw/expanded_polynomial.json')),
        'natural_polynomial':verify_expansion(target,read(d/'natural/expanded_polynomial.json'))}
    if parent_directory:
        parent=read(Path(parent_directory)/'raw/raw_audit_input.json')
        def prefix(m):
            rows=m['rows']
            end=next(i for i,r in enumerate(rows) if r['label']=='crt.nonnegative_evaluation')
            return rows[:end+1]
        pp=prefix(parent);mp=prefix(meta)
        if pp!=mp:
            parent_horizon=read(Path(parent_directory)/'SUMMARY.json')['horizon_minimum']
            new_horizon=read(d/'SUMMARY.json')['horizon_minimum']
            need(pp[0]['label']==mp[0]['label']=='addition','unexpected horizon gate')
            pp=copy.deepcopy(pp)
            constant=next(term for term in pp[0]['terms'] if term[1]==[])
            need(constant[0]==-parent_horizon,'unexpected parent horizon constant')
            constant[0]=-new_horizon
            receipt['horizon_replacement']={'parent':parent_horizon,'new':new_horizon,'changed_row':0}
        need(pp==mp,'semantic prefix differs from exact parent beyond recorded horizon')
        receipt['identical_semantic_prefix_rows']=len(prefix(meta))
    bad=copy.deepcopy(cert)
    bad['steps'][0]['restoration'][0][0]+=1
    try:
        verify_contraction(raw,target,bad)
    except ValueError:
        receipt['negative_control_changed_restoration']='rejected'
    else:
        raise ValueError('corrupted restoration accepted')
    p=read(d/'natural/expanded_polynomial.json')
    p['terms'][0][0]+=1
    try:
        verify_expansion(target,p)
    except ValueError:
        receipt['negative_control_changed_coefficient']='rejected'
    else:
        raise ValueError('corrupted polynomial accepted')
    receipt['sha256']={str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [d/'raw/equation.json',d/'natural/equation.json',d/'natural/expanded_polynomial.json',d/'natural/elimination_certificate.json']}
    receipt['status']='all exact checks passed'
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('directory',type=Path)
    p.add_argument('--parent',type=Path)
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    result=check(a.directory,a.parent)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:
        a.output.write_text(text)
    print(text)
