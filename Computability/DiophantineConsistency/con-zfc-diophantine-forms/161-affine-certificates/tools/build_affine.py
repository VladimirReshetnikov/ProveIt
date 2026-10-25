#!/usr/bin/env python3
"""Emit affine-radix/odd-multiple quartics from the supplied factorial-free source.

Uses only Python's standard library. Every algebraic operation is exact.
This program does not establish the unbounded semantic proof.
"""
from __future__ import annotations
from pathlib import Path
from collections import defaultdict
import argparse, copy, hashlib, json, zipfile

BASE = Path(__file__).resolve().parent
ARCHIVE = BASE.parent / 'provenance' / 'ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip'
PREFIX = 'ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct/'

def norm(terms):
    p = defaultdict(int)
    for c, m in terms:
        if type(c) is not int or any(type(i) is not int for i in m):
            raise ValueError('noninteger polynomial datum')
        p[tuple(sorted(m))] += c
    return {m:c for m,c in p.items() if c}

def add(*polys):
    p=defaultdict(int)
    for q in polys:
        for m,c in q.items(): p[m]+=c
    return {m:c for m,c in p.items() if c}

def mul(p,q):
    r=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items(): r[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in r.items() if c}

def substitute(p,i,q):
    r={}
    for m,c in p.items():
        t={():c}
        for j in m: t=mul(t,q if j==i else {(j,):1})
        r=add(r,t)
    return r

def terms(p): return [[c,list(m)] for m,c in sorted(p.items())]
def canonical(obj): return (json.dumps(obj,ensure_ascii=False,indent=2,sort_keys=True)+'\n').encode()
def put(p,obj): p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(canonical(obj))

def construct(source, profile):
    old=copy.deepcopy(source)
    names={v['name']:i for i,v in enumerate(old['variables'])}
    q=names['pow2.output'];z=names['radix.odd_square_root_half']
    s=names['beta.odd_square_multiplier'];v=names['beta.odd_square_root_half']
    labels={r['label']:i for i,r in enumerate(old['residuals'])}
    rq=labels['radix.odd_square'];rs=labels['beta.odd_square_multiplier']
    rows=[norm(r['terms']) for r in old['residuals']]
    if rows[rq]!={():-2,(q,):1,(z,):-4,(z,z):-4}: raise ValueError('unexpected translated radix row')
    if rows[rs]!={():-1,(s,):1,(v,):-4,(v,v):-4}: raise ValueError('unexpected beta multiplier row')
    before_q=rows[rq];before_s=rows[rs]
    rows[rq]={():-2,(q,):1,(z,):-4}
    rows[rs]={():-1,(s,):1,(v,):-2}
    changed=copy.deepcopy(old)
    changed['variant']='affine_radix_odd_beta_before_projection_'+profile
    changed['residuals'][rq]['terms']=terms(rows[rq]);changed['residuals'][rq]['label']='radix.one_mod_four'
    changed['residuals'][rs]['terms']=terms(rows[rs]);changed['residuals'][rs]['label']='beta.odd_multiplier'
    restored_q={():2,(z,):4};restored_s={():1,(v,):2}
    projected=[substitute(substitute(r,q,restored_q),s,restored_s) for r in rows]
    if projected[rq] or projected[rs]: raise ValueError('nonzero pivot row after substitution')
    if any(len(m)>2 for r in projected for m in r):raise ValueError('projection raised row degree')
    keep_vars=[i for i in range(len(old['variables'])) if i not in (q,s)]
    keep_rows=[i for i in range(len(rows)) if i not in (rq,rs)]
    reindex={i:j for j,i in enumerate(keep_vars)}
    new=copy.deepcopy(changed)
    new['variant']='affine_radix_odd_beta_'+profile
    new['variables']=[copy.deepcopy(old['variables'][i]) for i in keep_vars]
    new['variables'][reindex[z]]['name']='radix.one_mod_four_parameter'
    new['variables'][reindex[v]]['name']='beta.odd_multiplier_parameter'
    new['residuals']=[dict(old['residuals'][i],terms=terms({tuple(reindex[j] for j in m):c for m,c in projected[i].items()})) for i in keep_rows]
    for r in new['residuals']:
        if r['label']=='bootstrap.beta_base_square_product':r['label']='bootstrap.beta_base_odd_product'
    P={}
    for r in new['residuals']:
        rr=norm(r['terms']);P=add(P,mul(rr,rr))
    used={i for m in P for i in m}
    if used!=set(range(len(new['variables']))):raise ValueError('unconstrained advertised variable')
    metrics={'domain':'unrestricted integers','variables':len(new['variables']),'quadratic_residuals':len(new['residuals']),'degree':max(map(len,P)),'collected_monomials':len(P),'coefficient_height':max(map(abs,P.values())),'residual_height':max(abs(c) for r in new['residuals'] for c,_ in r['terms'])}
    certificate={'schema':'affine_radix_odd_beta_projection_v1','profile':profile,'source_sha256':hashlib.sha256(canonical(source)).hexdigest(),'mutations':[{'row':rq,'before':terms(before_q),'after':terms(rows[rq]),'meaning':'actual q = stored coordinate minus 1 = 4z+1'},{'row':rs,'before':terms(before_s),'after':terms(rows[rs]),'meaning':'s=2v+1; y=Fs retained'}],'eliminated':[{'variable':q,'row':rq,'replacement':terms(restored_q)},{'variable':s,'row':rs,'replacement':terms(restored_s)}],'retained_original_variables':keep_vars,'retained_original_rows':keep_rows,'restoration_convention':'old nonpivot coordinates equal corresponding new coordinates; restore q and s by listed affine polynomials','equation_sha256':hashlib.sha256(canonical(new)).hexdigest()}
    return changed,new,{'schema':'collected_integer_polynomial_v1','variables':len(new['variables']),'terms':terms(P)},certificate,metrics

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--archive',type=Path,default=ARCHIVE);ap.add_argument('--output',type=Path,default=BASE.parent/'stages'/'affine');args=ap.parse_args()
    with zipfile.ZipFile(args.archive) as z:
        for profile in ('principal','companion'):
            raw=z.read(PREFIX+profile+'/equation.json'); source=json.loads(raw)
            changed,eq,poly,cert,metrics=construct(source,profile)
            cert['archive_sha256']=hashlib.sha256(args.archive.read_bytes()).hexdigest()
            cert['source_member']=PREFIX+profile+'/equation.json'
            cert['source_member_sha256']=hashlib.sha256(raw).hexdigest()
            out=args.output/profile
            for name,obj in [('mutated_source.json',changed),('equation.json',eq),('expanded_polynomial.json',poly),('certificate.json',cert),('metrics.json',metrics)]:put(out/name,obj)
            print(profile,json.dumps(metrics,sort_keys=True))

if __name__=='__main__':main()
