#!/usr/bin/env python3
"""Exact coefficient-only checks of the general-level character formula."""
from math import comb,gcd
from collections import defaultdict
from pathlib import Path
import json
from package_io import read_json
import sympy as sp

def canonical(N,a,b,r,s):
    r%=N;s%=N
    pair=(r,s);inv=((-r)%N,(-s)%N)
    if pair==inv:return None,0
    return ((a,b,*pair),1) if pair<inv else ((a,b,*inv),-1)

def matrix(N,w):
    keys=set()
    for a in range(1,w):
        for r in range(N):
            for s in range(N):
                key,sgn=canonical(N,a,w-a,r,s)
                if key and not(key[0]==1 and key[2]==0):keys.add(key)
    keys=sorted(keys);idx={k:i for i,k in enumerate(keys)};rows=[]
    def row(terms):
        z=defaultdict(int)
        for c,a,b,r,s in terms:
            key,sign=canonical(N,a,b,r,s)
            if key:z[key]+=c*sign
        z={k:c for k,c in z.items() if c}
        assert all(k in idx for k in z)
        if z:rows.append([z.get(k,0) for k in keys])
    for p in range(1,w):
        q=w-p
        for r in range(N):
            for s in range(N):
                st=[(1,p,q,r,s),(1,q,p,s,r)]
                sh=[(comb(q+j-1,j),q+j,p-j,s,r-s) for j in range(p)]
                sh +=[(comb(p+j-1,j),p+j,q-j,r,s-r) for j in range(q)]
                if (p==1 and r==0) or (q==1 and s==0):
                    row(st+[(-c,a,b,r0,s0) for c,a,b,r0,s0 in sh])
                else:row(st);row(sh)
    return keys,sp.Matrix(rows)

def predicted_nullity(N,w):
    if w%2==0:return 0
    d=(N*N-gcd(N,2)**2)//2
    eps={1:0,3:1,5:-1}[w%6]
    num=d*(w-1)+(1-gcd(N,3))*eps
    assert num%6==0
    return num//6

def verify():
    results=[]
    for N in range(3,10):
        for w in (3,4,5):
            keys,M=matrix(N,w)
            rk=M.rank();null=M.cols-rk
            assert null==predicted_nullity(N,w),(N,w,null)
            print('PASS level',N,'weight',w,'columns',M.cols,'rank',rk,'nullity',null,flush=True)
            results.append({'level':N,'weight':w,'columns':M.cols,
                            'exact_rank':rk,'nullity':null})
    assert results == read_json('general_level_rank_receipt.json'), 'General-level reference receipt changed'
    return results

if __name__=='__main__':
    verify()
