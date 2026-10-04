#!/usr/bin/env python3
"""Fresh sparse highest-homogeneous computation for the two dominating recoder residuals."""
import json,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def addpoly(a,b,sign=1):
    p=dict(a)
    for m,c in b.items():
        p[m]=p.get(m,0)+sign*c
        if not p[m]:del p[m]
    return p

def mulpoly(a,b):
    p={}
    for x,c in a.items():
        for y,d in b.items():
            z=dict(x)
            for k,v in y:z[k]=z.get(k,0)+v
            mon=tuple(sorted(z.items()));p[mon]=p.get(mon,0)+c*d
    return {m:c for m,c in p.items()if c}

def calc():
    data=json.loads((ROOT/'data/pair_inline-dag.json').read_text())
    env={n:(1,{((n,1),):1})for n in data['witnesses']+['RawLeft','RawRight']}
    env['G']=(576000,{(('History:W',576000),):1})
    def read(x):return (0,{():x}if x else{})if type(x)is int else env[x]
    def combine(op,a,b):
        da,pa=a;db,pb=b
        if op=='*':return da+db,mulpoly(pa,pb)
        if da>db:return da,pa
        if db>da:return db,{m:(c if op=='+'else-c)for m,c in pb.items()}
        return da,addpoly(pa,pb,1 if op=='+'else-1)
    for out,op,a,b in data['nodes']:env[out]=combine(op,read(a),read(b))
    top=[]
    for i,(a,b)in enumerate(data['equations']):
        deg,poly=combine('-',read(a),read(b))
        if deg==1152000:
            if poly!={(('History:W',1152000),):-1}:raise RuntimeError('Unexpected leading homogeneous part')
            top.append({'pair_residual':i,'initializer_residual':i+3,'global_residual':i+51,'degree':deg,'leading_coefficient':-1,'leading_variable':'History:W','leading_exponent':1152000})
    if [r['pair_residual']for r in top]!=[13,127]:raise RuntimeError('Unexpected maximal residuals')
    for name in['two-input-receipt.json','one-input-receipt.json']:
        r=json.loads((ROOT/name).read_text());bounds=r['residual_degree_bounds']
        if [i for i,d in enumerate(bounds)if d==1152000]!=[64,178]:raise RuntimeError('Global top positions changed')
        if max(d for d in bounds if d<1152000)!=1127949:raise RuntimeError('Degree gap changed')
    return {'status':'PASS_FRESH_EXACT_LEADING_HOMOGENEOUS_CHECK','recoder_sha256':hashlib.sha256((ROOT/'data/pair_inline-dag.json').read_bytes()).hexdigest(),'top_residuals':top,'all_other_global_residual_upper_bounds_at_most':1127949,'exact_final_degree':2304000,'exact_final_leading_part':'2*History:W^2304000','method':'Independently multiply/add sparse upper-homogeneous polynomials through the recoder JSON, after G=W^576000; nonzero resulting leading polynomials certify exactness.'}
if __name__=='__main__':print(json.dumps(calc(),indent=2))
