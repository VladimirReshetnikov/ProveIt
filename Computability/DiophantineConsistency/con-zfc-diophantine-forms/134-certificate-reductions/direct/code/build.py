#!/usr/bin/env python3
"""Rebuild the signed deterministic-center quartic from the frozen parent.

Only standard-library arithmetic and the retained exact projection/translation
helpers are used. This program produces finite polynomial artifacts; the
unbounded semantic justification is in ../proof.md.
"""
from pathlib import Path
from collections import defaultdict
import argparse,copy,hashlib,json
import terminal_elimination as E
import translate_coordinates as T

ROOT=Path(__file__).resolve().parents[1]
def add(*ps):
    q=defaultdict(int)
    for p in ps:
        for m,c in p.items():q[m]+=c
    return {m:c for m,c in q.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def var(v):return {(v,):1}
def put(d,n,x):
    d.mkdir(parents=True,exist_ok=True);(d/n).write_bytes(E.canonical_bytes(x))
def sha(x):return hashlib.sha256(E.canonical_bytes(x)).hexdigest()

def change_source():
    old=json.loads((ROOT/'baseline/factored.json').read_text())
    c=json.loads((ROOT/'baseline/interfaces.json').read_text())
    e=copy.deepcopy(old);names={v['name']:i for i,v in enumerate(e['variables'])}
    W,A=names['shared.W'],names['shared.A']
    anchor=c['seed_data'][-1];X,Y=anchor['pair'];h=E.normalize(anchor['exponent'])
    U0,C0=c['cap_variables']['U'],c['cap_variables']['Y']
    H,B,eta=[c['cap_variables'][k] for k in ('H','B','e')]
    H2=len(e['variables']);e['variables'].append({'name':'new_center.H2','kind':'gate'})
    guardA=next(i for i,g in enumerate(c['guards']) if g.get('coordinate')==A)
    guardEta=next(i for i,g in enumerate(c['guards']) if g['kind']=='anchor_common_multiplier')
    guardCap=next(i for i,g in enumerate(c['guards']) if g['kind']=='shared_square_cap')
    removed={'cap.main_Ay','cap.main_norm','cap.comparison_constructor','cap.comparison_modulus',f'domain_guard.{guardA}',f'domain_guard.{guardEta}'}
    changes=[];rows=[]
    for r in e['residuals']:
        p=E.normalize(r['terms']);before=p
        if r['label'] in removed:
            changes.append({'old':r,'new':None});continue
        p=E.substitute(E.substitute(p,U0,var(X)),C0,var(Y))
        if r['label']=='cap.index_residue':p=add(p,var(W),neg(h))
        if r['label']=='shared.frame_definition':p=add(p,p,neg(var(W)))
        if r['label']=='cap.common_multiple':p=E.substitute(p,eta,{(eta,):2})
        if r['label']==f'domain_guard.{guardCap}':
            # Old C-W-1-sum(all Yi^2)-N3 becomes
            # C^2-W^2-1-sum(non-anchor Yi^2)-N3.
            p=add(p,neg(var(Y)),{(Y,Y):2},var(W),{(W,W):-1})
        rr=dict(r,terms=E.as_terms(p))
        if p!=before:changes.append({'old':r,'new':rr})
        if E.degree(p)>2:raise ValueError('Nonquadratic transformed row')
        rows.append(rr)
    newrows=[
        {'label':'new_center.H2','terms':E.as_terms(add(var(H2),{(H,H):-1}))},
        {'label':'new_center.definition','terms':E.as_terms(add(var(B),neg(var(A)),E.multiply(add(var(A),{():-1}),var(H2))))},
    ]
    e['residuals']=rows+newrows;e['variant']+=':signed_semantic_fixed_center';e.pop('metrics',None)
    cert={'schema':'signed_semantic_fixed_center_v1','parent_sha256':sha(old),'source_sha256':sha(e),'changes':changes,'appended_rows':newrows,'anchor_pair':[X,Y],'anchor_index':E.as_terms(h),'old_anchor_pair':[U0,C0],'frame':W,'scale':A,'square_wire':H2,'removed_guards':[guardA,guardEta],'cap_guard':guardCap,'semantics':'Existence equivalence proved in proof.md; old private witnesses need not be preserved.'}
    return e,cert

def centered(eq,base,initial):
    rows=[E.normalize(r['terms']) for r in eq['residuals']]
    squares=[E.multiply(p,p) for p in rows];total=add(*squares);shifts={};history=[]
    def update(q,p,k):
        for m,c in p.items():
            q[m]=q.get(m,0)+k*c
            if not q[m]:q.pop(m)
    def score(p):return max(map(abs,p.values())),len(p),sum(map(abs,p.values()))
    best=score(total)
    for stage in range(8):
        changed=False
        for v,meta in enumerate(eq['variables']):
            if meta['kind']=='integer_guard':continue
            hits=[i for i,p in enumerate(rows) if any(v in m for m in p)];options=[]
            for d in (-8,-4,-3,-2,-1,1,2,3,4,8):
                nr={i:E.substitute(rows[i],v,{(v,):1,():d}) for i in hits}
                ns={i:E.multiply(p,p) for i,p in nr.items()};nt=total.copy()
                for i in hits:update(nt,squares[i],-1);update(nt,ns[i],1)
                s=score(nt)
                if s<best:options.append((s,abs(d),d,nr,ns,nt))
            if options:
                s,_,d,nr,ns,total=min(options,key=lambda z:z[:3]);best=s;changed=True
                for i in hits:rows[i]=nr[i];squares[i]=ns[i]
                shifts[v]=shifts.get(v,0)+d;history.append({'pass':stage,'variable':v,'shift':d,'score':list(s)})
        if not changed:break
    final=copy.deepcopy(eq)
    for r,p in zip(final['residuals'],rows):r['terms']=E.as_terms(p)
    final['variant']+=':finite_centering';combined=dict(initial)
    for v,d in shifts.items():combined[v]=combined.get(v,0)+d
    combined={v:d for v,d in combined.items() if d}
    if T.translate(base,combined)['residuals']!=final['residuals']:raise ValueError('Translation mismatch')
    cert={'schema':'integral_translation_v1','input_sha256':sha(base),'output_sha256':sha(final),'shifts':[[i,d] for i,d in sorted(combined.items())],'convention':'old=new+shift','search_history':history}
    return final,cert

def build(out):
    source,sc=change_source()
    projected,pc,_=E.optimize(source,max_support=16)
    finite=E.verify(source,projected,pc)
    shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'].endswith('minus1')}
    for i,v in enumerate(projected['variables']):
        if v['name']=='t0':shifts[i]=-16
    initial=T.translate(projected,shifts)
    eq,tc=centered(initial,projected,shifts);poly=E.expand(eq)
    metrics={'domain':'unrestricted integers','variables':len(eq['variables']),'residuals':len(eq['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'coefficient_height':max(abs(c) for c,m in poly['terms']),'residual_height':max(abs(c) for r in eq['residuals'] for c,m in r['terms'])}
    for n,x in [('source.json',source),('source_change.json',sc),('projected.json',projected),('projection.json',pc),('projection_check.json',finite),('translation.json',tc),('equation.json',eq),('expanded_polynomial.json',poly),('metrics.json',metrics)]:put(out,n,x)
    print(json.dumps(metrics,sort_keys=True));return metrics

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('output',type=Path);a=p.parse_args();build(a.output)
