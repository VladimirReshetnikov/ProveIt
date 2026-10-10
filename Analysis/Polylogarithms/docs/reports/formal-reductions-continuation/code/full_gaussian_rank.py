#!/usr/bin/env python3
"""Exact verification of the manuscript's Gaussian single-product rank conjecture.

The raw coefficient rows are generated independently of the polynomial nullspace
formulas. Only the Python standard library is required for basis certificates;
SymPy is optional for independent exact row-rank calculations.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction
from math import comb
from pathlib import Path
import argparse
import hashlib
import json

PAIRS = ((0,1),(1,0),(1,1),(1,2),(1,3),(2,1))
NAMES = ('U','G','A','K','M','V')

def add(row, key, value):
    if not value: return
    row[key] += value
    if not row[key]: del row[key]

def canonical(a, r, s):
    r %= 4; s %= 4
    if r % 2 == s % 2 == 0: return None, 0
    inv = ((-r)%4,(-s)%4)
    if (r,s) <= inv: return (a,r,s), 1
    return (a,*inv), -1

def rows_and_columns(w):
    """Keep only S−H when precisely one single factor is divergent."""
    cols = [(a,r,s) for a in range(1,w) for r,s in PAIRS
            if (a,r,s)!=(1,0,1)]
    pos = {c:i for i,c in enumerate(cols)}
    rows=[]; labels=[]
    def term(row,a,r,s,k):
        key,sgn=canonical(a,r,s)
        if sgn: add(row,key,k*sgn)
    for p in range(1,w):
        q=w-p
        for r in range(4):
            for s in range(4):
                S=defaultdict(int); H=defaultdict(int)
                term(S,p,r,s,1); term(S,q,s,r,1)
                for j in range(p):
                    term(H,q+j,s,r-s,comb(q+j-1,j))
                for j in range(q):
                    term(H,p+j,r,s-r,comb(p+j-1,j))
                divergences=int(p==1 and r==0)+int(q==1 and s==0)
                choices=[]
                if divergences==1:
                    R=defaultdict(int,S)
                    for key,v in H.items(): add(R,key,-v)
                    choices=[('regularized_difference',R)]
                elif divergences==0:
                    choices=[('stuffle',S),('shuffle',H)]
                # Two divergent factors occur only in a real row at w=2.
                for name,row in choices:
                    if not row: continue
                    assert (1,0,1) not in row, (w,p,r,s,name,row)
                    rr=[0]*len(cols)
                    for key,v in row.items(): rr[pos[key]]=v
                    rows.append(rr); labels.append((p,q,r,s,name))
    return rows, cols, labels

# Homogeneous polynomials are coefficient vectors: p[k] X^k Y^(n-k).
def transform(p, a,b,c,d):
    """Substitute (X,Y) -> (aX+bY,cX+dY), exactly."""
    n=len(p)-1; out=[0]*(n+1)
    for k,pk in enumerate(p):
        if not pk: continue
        for j in range(k+1):
            left=comb(k,j)*a**j*b**(k-j)
            if not left: continue
            for h in range(n-k+1):
                out[j+h] += pk*left*comb(n-k,h)*c**h*d**(n-k-h)
    return out

def vector_from_parameters(w,G,A):
    n=w-2; c=G[n]
    U=[-v for v in transform(G,0,1,1,0)]; U[0]+=c
    M=transform(G,1,-1,1,0)
    K=[-v for v in transform(A,0,1,-1,1)]
    V=[-v for v in transform(K,0,1,1,0)]
    polynomials=dict(zip(NAMES,(U,G,A,K,M,V)))
    assert U[0]==0
    _,cols,_=rows_and_columns(w)
    return [polynomials[NAMES[PAIRS.index((r,s))]][a-1] for a,r,s in cols]

def basis(w):
    if w%2==0:return [],[]
    n=w-2; m=(w-1)//2; vecs=[]; tags=[]
    # G_j = X^(2j) (2Y-X)^(n-2j), 0 <= j < m.
    for j in range(m):
        k=n-2*j
        G=[0]*(n+1)
        for h in range(k+1): G[2*j+h]=comb(k,h)*(-1)**h*2**(k-h)
        vecs.append(vector_from_parameters(w,G,[0]*(n+1)))
        tags.append({'sector':'G','j':j})
    # A_j = X^(n-j)Y^j - X^jY^(n-j), 0 <= j < m.
    for j in range(m):
        A=[0]*(n+1); A[n-j]=1; A[j]=-1
        vecs.append(vector_from_parameters(w,[0]*(n+1),A))
        tags.append({'sector':'A','j':j})
    return vecs,tags

def matvec(rows,v):return [sum(a*b for a,b in zip(row,v)) for row in rows]

def rational_rank(rows):
    # Independent exact elimination, included for small validation cases.
    pivots={}
    for rr in rows:
        r=list(map(Fraction,rr))
        for j,p in pivots.items():
            if r[j]:
                q=r[j];r=[x-q*y for x,y in zip(r,p)]
        lead=next((j for j,x in enumerate(r) if x),None)
        if lead is not None:
            q=r[lead];pivots[lead]=[x/q for x in r]
            pivots=dict(sorted(pivots.items()))
    return len(pivots)

def verify_weight(w, rank_check=False):
    rows,cols,labels=rows_and_columns(w); vecs,tags=basis(w)
    assert all(not any(matvec(rows,v)) for v in vecs)
    ng=[j for j,(a,r,s) in enumerate(cols) if (r,s)!=(1,0)]
    m=(w-1)//2 if w%2 else 0
    expected_rank=5*w-6 if w%2 else 6*w-7
    expected_ng_rank=(9*w-11)//2 if w%2 else 5*w-6
    result={'weight':w,'rows':len(rows),'columns':len(cols),
            'basis_size':len(vecs),'basis_residual_zero':True,
            'expected_rank':expected_rank,'expected_nong_rank':expected_ng_rank}
    if rank_check:
        result['rank']=rational_rank(rows)
        result['nong_rank']=rational_rank([[row[j] for j in ng] for row in rows])
        result['basis_rank']=rational_rank(vecs)
        assert result['rank']==expected_rank
        assert result['nong_rank']==expected_ng_rank
        assert result['basis_rank']==len(vecs)
    return result

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='full_gaussian_rank_results.json')
    args=parser.parse_args()
    checks=[verify_weight(w,rank_check=(w<=11)) for w in range(2,18)]
    checks += [verify_weight(w) for w in (23,31,47,63)]
    rows,cols,labels=rows_and_columns(5);vecs,tags=basis(5)
    # Match the manuscript's exact finite-system row and column counts.
    assert len(rows)==92 and len(cols)==23
    payload={'theorem':'Full Gaussian single-product coefficient module',
        'scope':'Conjugation, convergent depth-one shuffle and stuffle, and one-divergence stuffle-minus-shuffle only.',
        'not_claimed':'No numerical period independence and no completeness of the full double-shuffle algebra.',
        'checks':checks,
        'weight5':{'columns':cols,'row_labels':labels,'matrix':rows,'basis_tags':tags,'kernel_basis':vecs}}
    p=Path(args.output);p.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({'output':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                     'checks':checks},indent=2))
if __name__=='__main__': main()
