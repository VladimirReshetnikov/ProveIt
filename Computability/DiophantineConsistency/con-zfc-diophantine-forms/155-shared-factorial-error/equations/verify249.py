#!/usr/bin/env python3
"""Check the exact composition independently of its producer."""
import copy,json,sys
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'parent252/code'))
import terminal_elimination as E
def need(b,m):
    if not b:raise ValueError(m)
def read(p):return json.loads(p.read_text())
def sparse(ts):
    d=Counter()
    for c,m in ts:d[tuple(m)]+=c
    return {m:c for m,c in d.items() if c}
def terms(d):return [[c,list(m)] for m,c in sorted(d.items()) if c]
def plus(*ps):
    d=Counter()
    for p in ps:
        for m,c in p.items():d[m]+=c
    return {m:c for m,c in d.items() if c}
def multiply(a,b):
    d=Counter()
    for m,c in a.items():
        for n,e in b.items():d[tuple(sorted(m+n))]+=c*e
    return {m:c for m,c in d.items() if c}
def translated(p,shifts):
    out={}
    for m,c in p.items():
        a={():c}
        for v in m:a=multiply(a,{(v,):1,():shifts.get(v,0)})
        out=plus(out,a)
    return out
def audit(source,projected,pc,eq,poly,meta,tr):
    old=read(ROOT/'parent252/data/factored_source.json')
    md=read(ROOT/'parent252/upstream/parent/transform_certificate.json')
    ns={v['name']:i for i,v in enumerate(old['variables'])};A=ns['shared.A'];H=ns['cap.H'];f=ns['cap.f'];R=ns['cap.R'];C=md['cap_variables']['Y'];h=ns['cap.h'];q=ns['pow2.output'];z=len(old['variables'])
    anchor=sparse(md['anchor_index'])
    replacement={
      'cap.comparison_constructor':{'label':'cap.deterministic_factor','terms':terms({(f,):1,(H,):-1,tuple(sorted((A,H))):1})},
      'cap.index_residue':{'label':'cap.index_residue','terms':terms(plus({(R,):1,tuple(sorted((C,h))):-1},{m:-c for m,c in anchor.items()}))}
    }
    rows=[]
    for r in old['residuals']:
        if r['label'] in ['choose0.digit_bound','domain_guard.2']:continue
        rows.append(replacement.get(r['label'],r))
    rows.append({'label':'radix.odd_square','terms':terms({(q,):1,(z,z):-4,(z,):-4,():-1})})
    need(source['residuals']==rows,'Source delta differs')
    need(source['variables']==old['variables']+[{'name':'radix.odd_square_root_half','kind':'signed_witness'}],'Source variables differ')
    original_pool=next(r for r in old['residuals'] if r['label']=='cap.pooled_index_residue')
    need(next(r for r in source['residuals'] if r['label']=='cap.pooled_index_residue')==original_pool,'Squared orientation pool changed')
    checked=E.verify(source,projected,pc)
    shifts=dict(tr['shifts']);need(tr['convention']=='old=new+shift','Wrong translation convention')
    need(eq['variables']==projected['variables'],'Projected variables changed')
    need(len(eq['residuals'])==len(projected['residuals']),'Row count differs')
    acc={}
    for r,s in zip(projected['residuals'],eq['residuals']):
        p=translated(sparse(r['terms']),shifts)
        need(s['label']==r['label'] and sparse(s['terms'])==p,'Translation identity failed')
        need(max(map(len,p),default=0)<=2,'Nonquadratic row')
        acc=plus(acc,multiply(p,p))
    need(sparse(poly['terms'])==acc,'Complete coefficient identity failed')
    live={v for m in acc for v in m};need(live==set(range(len(eq['variables']))),'Inactive variable')
    actual={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(map(len,acc)),'monomials':len(acc),'height':max(map(abs,acc.values())),'row_height':max(abs(c) for r in eq['residuals'] for c,m in r['terms'])}
    need(meta==actual,'Metric mismatch')
    need(actual=={'variables':249,'rows':182,'degree':4,'monomials':5321,'height':128446,'row_height':256},'Unexpected profile')
    return actual,checked
def main():
    b=ROOT/'equation249';objects=[read(b/n) for n in ['source.json','projected.json','projection_certificate.json','equation.json','expanded_polynomial.json','METRICS.json','translation_certificate.json']]
    metrics,projection=audit(*objects)
    mutations=[]
    xx=copy.deepcopy(objects);next(r for r in xx[0]['residuals'] if r['label']=='cap.deterministic_factor')['terms'][0][0]+=1;mutations.append(('center coefficient',xx))
    xx=copy.deepcopy(objects);next(r for r in xx[0]['residuals'] if r['label']=='cap.index_residue')['terms'][0][0]+=1;mutations.append(('index residue',xx))
    xx=copy.deepcopy(objects);xx[3]['residuals'][0]['terms'][0][0]+=1;mutations.append(('translated final row',xx))
    xx=copy.deepcopy(objects);xx[4]['terms'][10][0]+=1;mutations.append(('collected coefficient',xx))
    rejected=[]
    for name,xx in mutations:
        try:audit(*xx)
        except ValueError:rejected.append(name)
        else:raise ValueError('Accepted corruption: '+name)
    print(json.dumps({'status':'PASS','optimized':bool(sys.flags.optimize),'metrics':metrics,'projection':projection,'rejected_controls':rejected},indent=2))
if __name__=='__main__':main()
