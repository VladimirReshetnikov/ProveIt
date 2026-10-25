#!/usr/bin/env python3
"""Exact finite-field rank certificates for two explicitly limited searches.

The modular computation proves characteristic-zero full rank because the
matrix has integer entries. It does not prove minimum arity or consistency.
Python 3.10+, standard library only. No construction-program imports.
"""
from pathlib import Path
from math import isqrt
from hashlib import sha256
import argparse,json

ROOT=Path(__file__).resolve().parent
PRIME=1000003

def require(condition,message):
    if not condition:raise ValueError(message)

def load_rows(path):
    raw=path.read_bytes();e=json.loads(raw);n=len(e['variables']);rows=[]
    require(e.get('domain')=='unrestricted integers','Incorrect domain')
    for r in e['residuals']:
        p={}
        for c,m in r['terms']:
            require(type(c) is int and c!=0,'Noninteger or zero coefficient')
            require(type(m) is list and len(m)<=2,'Invalid residual degree')
            require(all(type(i) is int and 0<=i<n for i in m),'Invalid coordinate')
            require(m==sorted(m),'Noncanonical monomial')
            m=tuple(m);require(m not in p,'Duplicate monomial');p[m]=c
        rows.append(p)
    require({i for r in rows for m in r for i in m}==set(range(n)),'Unused coordinate')
    return n,rows,sha256(raw).hexdigest()

def insert(row,basis,pivots):
    q={m:c%PRIME for m,c in row.items() if c%PRIME}
    while q:
        pivot=max(q,key=lambda m:(len(m),m))
        if pivot not in basis:
            lead=q[pivot];inv=pow(lead,-1,PRIME)
            basis[pivot]={m:c*inv%PRIME for m,c in q.items()}
            pivots.append([list(pivot),lead]);return True
        factor=q[pivot]
        for m,c in basis[pivot].items():
            value=(q.get(m,0)-factor*c)%PRIME
            if value:q[m]=value
            else:q.pop(m,None)
    return False

def certify(path):
    require(all(PRIME%d for d in range(2,isqrt(PRIME)+1)),'Modulus is not prime')
    n,rows,source_hash=load_rows(path)
    # Stack the exact Hessians. A diagonal x_i^2 coefficient contributes 2c.
    basis={};hpivots=[]
    for r in rows:
        h={}
        for m,c in r.items():
            if len(m)==2:
                i,j=m;h.setdefault(i,{})[(j,)]=h.setdefault(i,{}).get((j,),0)+c
                h.setdefault(j,{})[(i,)]=h.setdefault(j,{}).get((i,),0)+c
        for k,row in sorted(h.items()):insert(row,basis,hpivots)
    hrank=len(basis);require(hrank==n,'A common Hessian direction remains')
    # The rows are the parts of R_i and x_j R_i in degrees at least 2.
    basis={};pivots=[];processed=0;columns=set()
    for multiplier in [None]+list(range(n)):
        for r in rows:
            if multiplier is None:
                q={m:c for m,c in r.items() if len(m)>=2}
            else:
                q={tuple(sorted(m+(multiplier,))):c for m,c in r.items() if len(m)>=1}
            columns.update(q);processed+=1
            require(insert(q,basis,pivots),'A high-degree row dependency was found')
    expected=(n+1)*len(rows)
    require(processed==expected==len(basis),'Incomplete Macaulay matrix')
    pivot_bytes=(json.dumps(pivots,separators=(',',':'))+'\n').encode()
    receipt={'status':'PASS','equation_sha256':source_hash,'variables':n,'residuals':len(rows),
       'prime':PRIME,'prime_checked_by_trial_division':True,'common_hessian_column_rank':hrank,
       'macaulay_rows':processed,'macaulay_columns':len(columns),'macaulay_rank':len(basis),
       'multiplier_degree_at_most':1,'maximum_polynomial_degree':3,
       'selected_pivot_columns_and_leads_sha256':sha256(pivot_bytes).hexdigest(),
       'conclusion':'The common Hessian kernel is zero over Q, and no nonzero affine-linear multiplier vector makes an affine residual combination over Q.',
       'scope_limit':'No global or local minimum arity claim; higher-degree multipliers, nonlinear coordinate changes, new quadratic relations, and semantic changes are not excluded.'}
    return receipt,pivot_bytes

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--equation',type=Path,default=ROOT/'equation/equation.json');ap.add_argument('--output',type=Path,default=ROOT/'verification/rank.json');args=ap.parse_args()
    receipt,pivots=certify(args.equation)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    args.output.with_name('macaulay_pivots.json').write_bytes(pivots)
    print(json.dumps(receipt,sort_keys=True))
if __name__=='__main__':main()
