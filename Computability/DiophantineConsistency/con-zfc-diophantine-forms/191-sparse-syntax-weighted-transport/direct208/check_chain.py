#!/usr/bin/env python3
"""Independent checks of growth/horizon edits, projections and exact expansion."""
from pathlib import Path
import json,sys,hashlib,copy
from math import comb
from collections import defaultdict
ROOT=Path(__file__).resolve().parent
HELPERS=ROOT/'helpers'
sys.path.insert(0,str(HELPERS))
import audit_projection as A
import audit_optimizations as O
def require(c,m):
    if not c:raise ValueError(m)
def read(p):return json.loads(p.read_bytes())
def terms(p):return [[v,list(k)] for k,v in sorted(p.items()) if v]
def polynomial(ts):return {tuple(m):c for c,m in ts}
def substitution(p,t,z):
    out=defaultdict(int)
    for mon,c in p.items():
        k=mon.count(t);rest=[i for i in mon if i!=t]
        for j in range(k+1):out[tuple(sorted(rest+[z]*j))]+=c*comb(k,j)*2**(k-j)*4**j
    return {m:c for m,c in out.items() if c}
def audit_metrics(folder,e):
    expansion=defaultdict(int)
    for row in e['residuals']:
        ts=row['terms']
        for j,(a,m) in enumerate(ts):
            for k in range(j,len(ts)):
                b,n=ts[k];expansion[tuple(sorted(m+n))]+=a*b*(1 if j==k else 2)
    p={m:c for m,c in expansion.items() if c}
    expected=read(folder/'expanded_polynomial.json')
    require(p==polynomial(expected['terms']),'expanded coefficients')
    require({i for mon in p for i in mon}==set(range(len(e['variables']))),'live input coordinates')
    met={'variables':len(e['variables']),'rows':len(e['residuals']),'degree':max(map(len,p)),
         'monomials':len(p),'height':max(map(abs,p.values())),
         'row_height':max(abs(c) for row in e['residuals'] for c,m in row['terms'])}
    require(met==read(folder/'metrics.json'),'all metrics')
    return met

def main():
    base=ROOT/'stages'
    old=read(ROOT/'stages/local_sparse/equation.json');source=read(base/'source214/equation.json')
    n={v['name']:i for i,v in enumerate(old['variables'])}
    changes=[j for j,(r,s) in enumerate(zip(old['residuals'],source['residuals'])) if r!=s]
    require(len(changes)==1,'only growth row changed at this stage')
    j=changes[0];require(old['residuals'][j]['label']=='growth_pell.norm','growth norm binding')
    X,Z,F=[n[k] for k in ('growth_pell.X','growth_pell.tF','growth.F')]
    want={():-1,(X,X):1,tuple(sorted([Z,Z])):-64,tuple(sorted([Z,F])):-16}
    require(polynomial(source['residuals'][j]['terms'])==want,'literal center 8t+1')
    t=n['t0'];z=n['cofinal.horizon_root'];h=[j for j,r in enumerate(source['residuals']) if r['label']=='cofinal.horizon']
    require(len(h)==1,'unique horizon');h=h[0]
    require(polynomial(source['residuals'][h]['terms'])=={():-16,(t,):1,(z,z):-4},'original horizon')
    rebuilt=[]
    for j,r in enumerate(source['residuals']):
        if j!=h:rebuilt.append(dict(r,terms=terms(substitution(polynomial(r['terms']),t,z))))
    live=sorted({i for r in rebuilt for _,mon in r['terms'] for i in mon});ren={i:j for j,i in enumerate(live)}
    rebuilt=[dict(r,terms=[[c,[ren[i] for i in mon]] for c,mon in r['terms']]) for r in rebuilt]
    affine=read(base/'affine213/equation.json');require(rebuilt==affine['residuals'],'complete affine substitution')
    require(len(affine['variables'])==213 and len(affine['residuals'])==153,'affine dimensions')
    metrics={'source214':audit_metrics(base/'source214',source),'affine213':audit_metrics(base/'affine213',affine)}
    cert=read(base/'radical208/certificate.json');e=affine;rejections=[]
    for step in cert['steps']:
        for label in ('slope','pivot','solution','hash'):
            bad=copy.deepcopy(step)
            if label=='slope':bad['slope']=-bad['slope']
            elif label=='pivot':
                for pair in bad['direction']:
                    if pair[0]==bad['pivot']:pair[1]+=1
            elif label=='solution':bad['sheared_pivot_solution'][0][0]+=1
            else:bad['output_sha256']='0'*64
            rejected=False
            try:A.one_step(e,bad,numerical_controls=False)
            except A.InvalidCertificate:rejected=True
            require(rejected,'projection mutation accepted: '+label)
            rejections.append(label)
        e=A.one_step(e,step,numerical_controls=False)
    require(e==read(base/'radical208/equation.json'),'entire independent radical reconstruction')
    metrics['radical']=audit_metrics(base/'radical208',e)
    chart_checks={}
    for folder in [ROOT/'equations/principal208']:
        if not (folder/'equation.json').exists():continue
        target=read(folder/'equation.json');ops=read(folder/'certificate.json')['operations'];dimension=len(e['variables'])
        old_rows=[O.sparse(r['terms'],dimension) for r in e['residuals']]
        new_rows=[O.sparse(r['terms'],dimension) for r in target['residuals']]
        require(O.apply(old_rows,ops,dimension)==new_rows,'forward chart/basis identities')
        require(O.apply(new_rows,ops,dimension,inverse=True)==old_rows,'inverse chart/basis identities')
        chart_checks[folder.name]={'operations':len(ops),'metrics':audit_metrics(folder,target)}
    print(json.dumps({'status':'PASS','growth_center':'8*t+1','horizon':'2+4*z','projection_steps':len(cert['steps']),
                      'projection_mutations_rejected':len(rejections),'metrics':metrics,'charts':chart_checks},sort_keys=True))
if __name__=='__main__':main()
