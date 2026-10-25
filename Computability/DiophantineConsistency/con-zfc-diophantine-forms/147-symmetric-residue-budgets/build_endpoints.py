#!/usr/bin/env python3
"""Rebuild the explicit quartics after the supplied reversible row operations."""
from pathlib import Path
from collections import defaultdict, Counter
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parent
PROFILES={'P258':'odd_three_pools_centered','P261':'four_pools_centered'}

def read(p):return json.loads(p.read_text())
def canonical(d):return (json.dumps(d,indent=2,sort_keys=True)+'\n').encode()
def sparse(terms):return {tuple(m):int(c) for c,m in terms if c}
def rowadd(a,b,k):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+k*c
        if not out[m]:del out[m]
    return out
def sos(rows):
    out=defaultdict(int)
    for r in rows:
        for a,c in r.items():
            for b,d in r.items():out[tuple(sorted(a+b))]+=c*d
    return {m:c for m,c in out.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]

def latex_term(c,m,first=False):
    sign=('-' if c<0 else ('' if first else '+'))
    mono=''.join('x_{%d}'%i+('^{%d}'%n if n>1 else '') for i,n in sorted(Counter(m).items()))
    return sign+(str(abs(c)) if abs(c)!=1 or not mono else '')+mono
def tex_rows(rows):
    out=['% Generated literal quadratic residuals. Parsed back by verify.py.']
    for i,r in enumerate(rows):
        chunks=[];part='';weight=0
        for j,(m,c) in enumerate(sorted(r.items())):
            t=latex_term(c,m,j==0)
            w=1.5+1.2*len(str(abs(c)))+3*len(m)
            if part and weight+w>68:
                chunks.append(part);part='';weight=0
            part+=t;weight+=w
        if part:chunks.append(part)
        expr=('\\\\\n&{}').join(chunks)
        out.append('\\[\\begin{aligned}\nr_{%d}&=%s\n\\end{aligned}\\]'%(i,expr))
    return '\n'.join(out)+'\n'

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    summary={}
    for name,profile in PROFILES.items():
        src=ROOT/'direct'/profile/'equation.json';d=read(src)
        rs=[sparse(r['terms']) for r in d['residuals']]
        ops=read(ROOT/'equations'/name/'row_operations.json')
        for i,j,k in ops:
            if i==j or not all(isinstance(v,int) for v in (i,j,k)):raise ValueError('invalid elementary operation')
            rs[i]=rowadd(rs[i],rs[j],k)
        d['residuals']=[{'label':f'residual_{i}','terms':terms(r)} for i,r in enumerate(rs)]
        d['variant']='symmetric_residue_budget_with_reversible_residual_reduction'
        d['row_reduction_source_sha256']=hashlib.sha256(src.read_bytes()).hexdigest()
        p=sos(rs);n=len(d['variables'])
        metrics={'variables':n,'residuals':len(rs),'degree':max(map(len,p)),
                 'monomials':len(p),'height':max(map(abs,p.values())),
                 'row_height':max(abs(c) for r in rs for c in r.values()),
                 'row_monomial_occurrences':sum(map(len,rs)),'row_operations':len(ops)}
        poly={'schema':'sparse_polynomial_v1','variables':n,'terms':terms(p)}
        files={'equation.json':canonical(d),'expanded_polynomial.json':canonical(poly),'METRICS.json':canonical(metrics),
               'residuals.tex':tex_rows(rs).encode(),'variables.tsv':('index\tname\tkind\n'+''.join(f"{i}\t{v['name']}\t{v['kind']}\n" for i,v in enumerate(d['variables']))).encode()}
        for f,b in files.items():
            path=ROOT/'equations'/name/f
            if a.check:
                if path.read_bytes()!=b:raise ValueError('reconstruction mismatch: '+str(path))
            else:path.write_bytes(b)
        summary[name]=metrics
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
