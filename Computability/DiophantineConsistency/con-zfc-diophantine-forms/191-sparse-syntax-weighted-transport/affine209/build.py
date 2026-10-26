#!/usr/bin/env python3
"""Exact affine-horizon substitution for the pinned 210-variable source."""
from pathlib import Path
import argparse, copy, hashlib, json

ROOT=Path(__file__).resolve().parent

def polynomial(ts):
    return {tuple(m):c for c,m in ts if c}

def terms(p):
    return [[v,list(k)] for k,v in sorted(p.items()) if v]

def add(a,b):
    c=dict(a)
    for m,v in b.items():
        c[m]=c.get(m,0)+v
        if not c[m]:del c[m]
    return c

def mul(a,b):
    c={}
    for m,v in a.items():
        for n,w in b.items():
            k=tuple(sorted(m+n));c[k]=c.get(k,0)+v*w
    return {k:v for k,v in c.items() if v}

def subst(p,t,z,minimum):
    out={}
    for mon,c in p.items():
        q={():c}
        for j in mon:
            q=mul(q,{():minimum,(z,):2*minimum} if j==t else {(j,):1})
        out=add(out,q)
    return out

def canonical(x):
    return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()

def build(minimum=16,check=False):
    raw=(ROOT/'source/parent210.json').read_bytes()
    old=json.loads(raw)
    names=[v['name'] for v in old['variables']]
    t=names.index('t0');z=names.index('cofinal.horizon_root')
    horizon=[i for i,r in enumerate(old['residuals']) if r['label']=='cofinal.horizon']
    if len(horizon)!=1:raise ValueError('ambiguous horizon')
    h=horizon[0]
    if polynomial(old['residuals'][h]['terms'])!={():-16,(t,):1,(z,z):-4}:
        raise ValueError('unexpected parent horizon')
    kept=[i for i in range(len(names)) if i!=t];ren={v:i for i,v in enumerate(kept)}
    eq=copy.deepcopy(old)
    eq['variables']=[copy.deepcopy(old['variables'][i]) for i in kept]
    eq['variables'][ren[z]]={'kind':'signed_horizon_parameter','name':'horizon.affine_parameter'}
    eq['residuals']=[]
    for i,r in enumerate(old['residuals']):
        if i==h:continue
        p=subst(polynomial(r['terms']),t,z,minimum)
        eq['residuals'].append({'label':r['label'],'terms':terms({tuple(ren[j] for j in k):v for k,v in p.items()})})
    eq.update(schema='conzfc-affine-pell-growth-v1',parent_equation_sha256=hashlib.sha256(raw).hexdigest(),
              variant='affine_horizon_'+str(minimum),horizon_minimum=minimum,
              semantic_change='t=minimum*(2*z+1); positivity recovered by q^t')
    expansion={}
    for row in eq['residuals']:
        p=polynomial(row['terms']);expansion=add(expansion,mul(p,p))
    met={'variables':len(eq['variables']),'rows':len(eq['residuals']),
         'degree':max(map(len,expansion)),'monomials':len(expansion),
         'height':max(map(abs,expansion.values())),
         'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms']),
         'residual_monomials':sum(len(r['terms']) for r in eq['residuals'])}
    cert={'schema':'affine-horizon-projection-v1','parent_sha256':hashlib.sha256(raw).hexdigest(),
          'deleted_row':h,'deleted_coordinate':t,'retained_parameter_old_index':z,
          'minimum':minimum,'new_horizon_row':terms({():-minimum,(t,):1,(z,):-2*minimum}),
          'restore_t':terms({():minimum,(ren[z],):2*minimum}),'kept_old_indices':kept,
          'output_sha256':hashlib.sha256(canonical(eq)).hexdigest()}
    products={'equation.json':eq,'expanded_polynomial.json':{'schema':'sparse-polynomial-v1','variables':len(kept),'terms':terms(expansion)},
              'metrics.json':met,'certificate.json':cert}
    folder=ROOT/'profiles'/('minimum'+str(minimum));folder.mkdir(exist_ok=True)
    for name,ob in products.items():
        path=folder/name;content=canonical(ob)
        if check:
            if path.read_bytes()!=content:raise ValueError(('rebuild mismatch',str(path)))
        else:path.write_bytes(content)
    return met

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--minimum',type=int,default=16);ap.add_argument('--check',action='store_true')
    args=ap.parse_args();print(json.dumps(build(args.minimum,args.check),sort_keys=True))
