#!/usr/bin/env python3
"""Rebuild the frozen row-exposure endpoints, without optimization or network."""
import argparse, json, hashlib
from pathlib import Path

def plus(*args):
    z={}
    for p in args:
        for m,c in p.items():z[m]=z.get(m,0)+c
    return {m:c for m,c in z.items() if c}
def scale(p,k):return {m:c*k for m,c in p.items() if c*k}
def times(p,q):
    z={}
    for m,c in p.items():
        for n,d in q.items():
            t=tuple(sorted(m+n));z[t]=z.get(t,0)+c*d
    return {m:c for m,c in z.items() if c}
def decode(terms):return {tuple(m):c for c,m in terms}
def encode(p):return [[c,list(m)] for m,c in sorted(p.items())]
def substitute(p,t,replacement):
    z={}
    for m,c in p.items():
        v={():c}
        for j in m:v=times(v,replacement if j==t else {(j,):1})
        z=plus(z,v)
    return z
def construct(source,certificate):
    rows=[decode(r['terms']) for r in source['residuals']]
    names={v['name']:i for i,v in enumerate(source['variables'])}
    for target,inputs in certificate['coordinate_shears']:
        t=names[target];replacement={(t,):1}|{(names[n],):c for n,c in inputs.items()}
        rows=[substitute(r,t,replacement) for r in rows]
    for i,j,k in certificate['affine_exposure_row_operations']:
        rows[i]=plus(rows[i],scale(rows[j],k))
    removed=[];removed_vars=[]
    for step in certificate['affine_projections']:
        i,t=step['row'],step['variable'];replacement=decode(step['replacement'])
        if rows[i].get((t,)) not in (-1,1) or max(map(len,rows[i]))>1:raise ValueError('nonunit affine row')
        if substitute(rows[i],t,replacement):raise ValueError('projection is not exact')
        rows=[substitute(r,t,replacement) for r in rows]
        if rows[i]:raise ValueError('dropped row is not zero')
        removed.append(i);removed_vars.append(t)
    keep=[i for i in range(len(source['variables'])) if i not in removed_vars]
    ren={i:j for j,i in enumerate(keep)}
    rows=[{tuple(ren[j] for j in m):c for m,c in r.items()} for i,r in enumerate(rows) if i not in removed]
    for i,j,k in certificate['final_row_operations']:rows[i]=plus(rows[i],scale(rows[j],k))
    polynomial=plus(*(times(r,r) for r in rows))
    equation={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':certificate['endpoint'],'variables':[source['variables'][i] for i in keep],'residuals':[{'label':f'row.{i:03d}','terms':encode(r)} for i,r in enumerate(rows)]}
    metrics={'variables':len(keep),'rows':len(rows),'degree':max(map(len,polynomial)),'monomials':len(polynomial),'height':max(map(abs,polynomial.values())),'row_degree':max(len(m) for r in rows for m in r),'row_height':max(abs(c) for r in rows for c in r.values()),'row_support':sum(map(len,rows)),'used_coordinates':sorted({i for m in polynomial for i in m})}
    return equation,{'schema':'expanded_integer_polynomial_v1','terms':encode(polynomial)},metrics
def dump(path,obj):path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')
def main():
    p=argparse.ArgumentParser();p.add_argument('--release',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path,required=True);a=p.parse_args();manifest=json.loads((a.release/'ENDPOINTS.json').read_text())
    for name,item in manifest['endpoints'].items():
        raw=(a.release/item['source']).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=item['source_sha256']:raise ValueError('source hash')
        cert=json.loads((a.release/item['certificate']).read_text());eq,poly,metrics=construct(json.loads(raw),cert);out=a.output/name;out.mkdir(parents=True,exist_ok=True)
        dump(out/'equation.json',eq);dump(out/'expanded_polynomial.json',poly);dump(out/'METRICS.json',metrics)
    print(json.dumps({'status':'built','endpoints':list(manifest['endpoints'])},sort_keys=True))
if __name__=='__main__':main()
