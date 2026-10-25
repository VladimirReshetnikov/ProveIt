#!/usr/bin/env python3
"""Independent name-level check of the complete canonical-sign source delta.

No import from the builder or contraction engine.  The large source circuit
is checked compositionally, using its literal factors and two tiny formal
polynomial identities rather than a gigantic expanded high-degree polynomial.
"""
from pathlib import Path
from collections import defaultdict
from copy import deepcopy
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parent
def need(b,m):
    if not b:raise ValueError(m)
def add(*ps):
    o=defaultdict(int)
    for p in ps:
        for m,c in p.items():o[m]+=c
    return {m:c for m,c in o.items() if c}
def sc(c,p):return {m:c*v for m,v in p.items() if c*v}
def mul(a,b):
    o=defaultdict(int)
    for m,c in a.items():
      for n,d in b.items():o[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in o.items() if c}
def at(x):return {(x,):1}
def sub(a,b):return add(a,sc(-1,b))
def row(eq,r):
    o={}
    for c,m in r['terms']:
        need(type(c) is int and c!=0,'coefficient')
        need(all(type(i)is int and 0<=i<len(eq['variables']) for i in m),'index')
        n=tuple(sorted(eq['variables'][i]['name'] for i in m));need(n not in o,'duplicate term');o[n]=c
    return o
def key(eq,r):return (r['label'],tuple(sorted(row(eq,r).items())))
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()

def verify(old,new):
    need(old['domain']==new['domain']=='nonnegative integers','domain')
    need(len({v['name'] for v in new['variables']})==len(new['variables']),'unique names')
    oldrows=[row(old,r) for r in old['residuals']]
    removed=[]
    def require_old(g,definition):
        p=sub(at(g),definition);hits=[i for i,r in enumerate(oldrows) if r==p]
        need(len(hits)==1,'old gate '+g);removed.append(hits[0])
    d=sub(at('crt.encoded.S'),at('crt.encoded.Sp'))
    ds=[d]+[sub(d,at(n)) for n in ('mul.339','mul.341','mul.343','mul.345','mul.347','mul.349','mul.351','mul.353')]
    ds += [sub(at('crt.encoded.a'),at('crt.encoded.c')),sub(at('crt.encoded.b'),at('crt.encoded.c')),
           sub(at('mul.355'),at('mul.357')),sub(d,at('mul.358')),
           sub(at('mul.363'),at('mul.369')),sub(at('mul.372'),at('mul.373'))]
    for i,p in enumerate(ds):require_old('sqd.'+str(i),mul(p,p))
    require_old('mul.355',mul(at('sqd.9'),at('sqd.10')))
    dd=add(at('crt.encoded.d'),{():2});require_old('mul.357',mul(dd,dd))
    p=mul(at('sqd.0'),at('sqd.1'));require_old('mul.374',p)
    for j in range(2,9):require_old('mul.'+str(373+j),mul(at('mul.'+str(372+j)),at('sqd.'+str(j))))
    require_old('mul.382',mul(at('mul.381'),add(at('sqd.11'),at('sqd.12'))))
    require_old('mul.383',mul(at('mul.382'),at('sqd.13')))
    require_old('mul.384',mul(at('mul.383'),at('sqd.14')))
    ev=[i for i,r in enumerate(old['residuals']) if r['label']=='crt.nonnegative_evaluation'];need(len(ev)==1,'old evaluation')
    need(oldrows[ev[0]]==add(at('mul.384'),at('sqd.15'),at('sqd.16'),sc(-1,at('mul.407'))),'old evaluated value')
    newrows=[row(new,r) for r in new['residuals']]
    fresh=[]
    def require_new(g,definition):
        g='oriented.'+g;p=sub(at(g),definition)
        hits=[i for i,r in enumerate(newrows) if r==p and new['residuals'][i]['label']==g]
        need(len(hits)==1,'new gate '+g);fresh.append(hits[0]);return at(g)
    gs=[sc(-1,p) for p in ds[:9]]+[sc(-1,ds[13]),ds[14]]
    p=gs[0]
    for i,g in enumerate(gs[1:],1):p=require_new('product'+str(i),mul(p,g))
    e=require_new('inequality_product',mul(ds[9],ds[10]))
    z=require_new('inequality_minus',mul(p,sub(e,dd)))
    z=require_new('inequality_branch',mul(z,add(e,dd)))
    w=require_new('axiom_branch',mul(p,sc(-1,ds[12])))
    nv=[i for i,r in enumerate(new['residuals']) if r['label']=='crt.oriented_nonnegative_evaluation'];need(len(nv)==1,'new evaluation')
    need(newrows[nv[0]]==add(mul(z,z),mul(w,w),at('sqd.15'),at('sqd.16'),sc(-1,at('mul.407'))),'new evaluated value')
    old_unchanged=[key(old,r) for i,r in enumerate(old['residuals']) if i not in set(removed+ev)]
    new_unchanged=[key(new,r) for i,r in enumerate(new['residuals']) if i not in set(fresh+nv)]
    need(old_unchanged==new_unchanged,'complete unchanged circuit')
    # Exact formal identities in four independent variables: no random testing.
    E,D,Q,G=map(at,['E','D','Q','G'])
    need(mul(sub(E,D),add(E,D))==sub(mul(E,E),mul(D,D)),'difference of squares')
    z=mul(Q,sub(mul(E,E),mul(D,D)));w=mul(Q,G)
    need(add(mul(z,z),mul(w,w))==mul(mul(Q,Q),add(mul(sub(mul(E,E),mul(D,D)),sub(mul(E,E),mul(D,D))),mul(G,G))),'factored disjunction')
    need(len(removed)==28 and len(set(removed))==28 and len(fresh)==14,'gate census')
    need((len(new['variables']),len(new['residuals']))==(310,262),'raw census')
    used={i for r in new['residuals'] for c,m in r['terms'] for i in m};need(used==set(range(310)),'live raw coordinates')
    need(all(len(m)<=2 for r in new['residuals'] for c,m in r['terms']),'quadratic raw rows')
    return {'status':'PASS','parent_variables':len(old['variables']),'parent_rows':len(old['residuals']),'new_variables':310,'new_rows':262,'removed_square_or_product_gates':28,'new_oriented_product_gates':14,'unchanged_rows':len(old_unchanged),'exact_compositional_polynomial_identity':True,'old_object_sha256':hashlib.sha256(canonical(old)).hexdigest(),'new_object_sha256':hashlib.sha256(canonical(new)).hexdigest(),'scope':'Complete finite circuit delta and local-source polynomial identity; canonical natural-domain completeness is the separate ordinary proof.'}

def main():
    a=argparse.ArgumentParser();a.add_argument('--parent',type=Path,default=ROOT/'inherited/cofinal_raw/equation.json');a.add_argument('--target',type=Path,default=ROOT/'raw/equation.json');a.add_argument('--output',type=Path);args=a.parse_args()
    old=json.loads(args.parent.read_text());new=json.loads(args.target.read_text());out=verify(old,new)
    mutations=[]
    x=deepcopy(new);x['residuals']=[r for r in x['residuals'] if r['label']!='crt.oriented_nonnegative_evaluation'];mutations.append(('missing source evaluation',x))
    x=deepcopy(new);next(r for r in x['residuals'] if r['label']=='oriented.axiom_branch')['terms'][0][0]+=1;mutations.append(('wrong branch factor',x))
    x=deepcopy(new);x['domain']='integers';mutations.append(('widened coordinate domain',x))
    x=deepcopy(new);x['residuals'][0]['terms'][0][0]+=1;mutations.append(('unrelated source change',x))
    rejects=[]
    for label,x in mutations:
      try:verify(old,x)
      except ValueError:rejects.append(label)
      else:raise ValueError('accepted negative control '+label)
    out['negative_controls']=rejects
    if args.output:args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
