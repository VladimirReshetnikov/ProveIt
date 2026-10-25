#!/usr/bin/env python3
"""Bounded pairwise integer row reduction; output is a replayable certificate."""
import argparse,json
from pathlib import Path
from build_affine import add,scale,mul,terms,decoded,canonical
ROOT=Path(__file__).resolve().parent
def dot(a,b):
    if len(a)>len(b):a,b=b,a
    return sum(c*b.get(m,0) for m,c in a.items())
def nearest(a,b):
    return (2*a+b)//(2*b)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--dense',action='store_true');ap.add_argument('--affine-radix',action='store_true');a=ap.parse_args()
    old=ROOT/(('candidate240_affine' if a.dense else 'candidate241_affine') if a.affine_radix else ('candidate241' if a.dense else 'candidate242'));target=ROOT/(('equation240' if a.dense else 'equation241_affine') if a.affine_radix else ('equation241' if a.dense else 'equation242'));target.mkdir(exist_ok=True)
    equation=json.loads((old/'equation.json').read_text());rows=[decoded(r) for r in equation['residuals']];norms=[dot(r,r) for r in rows];ops=[]
    for count in range(1500):
        best=None
        for i,p in enumerate(rows):
            for j,q in enumerate(rows):
                if i==j or not norms[j]:continue
                d=dot(p,q);k=nearest(d,norms[j]);gain=2*k*d-k*k*norms[j]
                if k and gain>0:
                    candidate=(gain,-abs(k),-i,-j,k)
                    if best is None or candidate>best:best=candidate
        if best is None:break
        gain,_,ni,nj,k=best;i=-ni;j=-nj;rows[i]=add(rows[i],scale(rows[j],-k));norms[i]=dot(rows[i],rows[i]);ops.append([i,j,-k])
    poly=add(*(mul(r,r) for r in rows));equation['residuals']=[{'label':f'row.{i:03d}','terms':terms(r)} for i,r in enumerate(rows)]
    metrics={'variables':len(equation['variables']),'rows':len(rows),'degree':max(map(len,poly)),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for r in rows for c in r.values()),'row_support':sum(map(len,rows))}
    transformation=json.loads((old/'transformation.json').read_text());transformation['final_row_operations']=ops
    equation['variant']+=':row_reduced'
    for name,data in [('equation.json',equation),('expanded_polynomial.json',{'schema':'expanded_integer_polynomial_v1','terms':terms(poly)}),('METRICS.json',metrics),('transformation.json',transformation),('RESTORATION.json',json.loads((old/'RESTORATION.json').read_text()))]:(target/name).write_bytes(canonical(data))
    print(json.dumps({'operations':len(ops),'metrics':metrics},sort_keys=True))
if __name__=='__main__':main()
