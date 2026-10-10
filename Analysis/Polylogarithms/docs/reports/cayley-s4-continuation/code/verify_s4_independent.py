#!/usr/bin/env python3
"""Second S4 verifier: placement shuffles and full antisymmetrized words.

Does not import the primary word-algebra implementation or its compressed
projection. Enumerates interleaving placements and ordered index merges.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json


def add(out, poly, factor=1):
    for w,c in poly.items():
        out[w]+=factor*c
        if not out[w]: del out[w]

def conjugation(w):
    return tuple({-1:-1,0:0,1:3,2:2,3:1}[a] for a in w)

def sh(u,v):
    ans=defaultdict(int)
    n=len(u)+len(v)
    for positions in combinations(range(n),len(u)):
        mask=set(positions);a=iter(u);b=iter(v)
        ans[tuple(next(a) if j in mask else next(b) for j in range(n))]+=1
    return ans

def shpoly(P,Q0):
    out=defaultdict(int)
    for u,a in P.items():
        for v,b in Q0.items(): add(out,sh(u,v),a*b)
    return out

def indexword(w):
    root_positions=[j for j,a in enumerate(w) if a!=-1]
    last_pos=-1;last_color=0;out=[]
    for j in root_positions:
        out.append((j-last_pos,(w[j]-last_color)%4))
        last_pos=j;last_color=w[j]
    if last_pos!=len(w)-1: raise ValueError('Trailing zero')
    return out

def wordof(indices):
    prefix=[];color=0
    for s,c in indices:
        color=(color+c)%4
        prefix += [-1]*(s-1)+[color]
    return tuple(prefix)

def stuffleword(u,v):
    x=indexword(u);y=indexword(v)
    stack=[(0,0,[])];out=defaultdict(int)
    while stack:
        i,j,seq=stack.pop()
        if i==len(x) and j==len(y):
            out[wordof(seq)]+=1
            continue
        if i<len(x):stack.append((i+1,j,seq+[x[i]]))
        if j<len(y):stack.append((i,j+1,seq+[y[j]]))
        if i<len(x) and j<len(y):
            stack.append((i+1,j+1,seq+[(x[i][0]+y[j][0],(x[i][1]+y[j][1])%4)]))
    return out

def D(w):
    table={-1:[(0,1),(2,-1)],0:[(-1,1),(2,1)],1:[(2,1),(3,-1)],
           2:[(2,1)],3:[(2,1),(1,-1)]}
    out=defaultdict(int)
    for choice in product(*(table[a] for a in w[::-1])):
        coeff=1
        for _,c in choice:coeff*=c
        out[tuple(a for a,_ in choice)]+=coeff
    return out

def antisym(P):
    out=defaultdict(int)
    add(out,P)
    for w,c in P.items():out[conjugation(w)]-=c
    return {w:c for w,c in out.items() if c}

def build_target():
    T=defaultdict(int)
    for w,c in [((-1,-1,-1,1,3),56),((-1,-1,-1,1,1),-408),
                ((-1,-1,1,-1,1),-192)]:add(T,antisym({w:1}),c)
    q={(1,):1,(3,):-1};qpower={():1}
    for _ in range(5):qpower=shpoly(qpower,q)
    add(T,qpower,-19)
    add(T,shpoly({(-1,-1,-1,1):1,(-1,-1,-1,3):-1},{(2,):1}),-112)
    return T

def verify(path):
    data=json.loads(path.read_text())
    R=defaultdict(Q)
    # odd(P) equality is equivalent to P-conj(P) equality.
    add(R,antisym(build_target()))
    for row in data['rows']:
        raw=defaultdict(int)
        if row['kind']=='double_shuffle':
            u,v=tuple(row['u']),tuple(row['v'])
            if not (u==(0,) or (u[0]!=0 and u[-1]!=-1)):
                raise ValueError('Invalid first factor')
            if v[0]==0 or v[-1]==-1:raise ValueError('Invalid second factor')
            add(raw,sh(u,v));add(raw,stuffleword(u,v),-1)
        elif row['kind']=='cayley':
            w=tuple(row['word']);add(raw,{w:1});add(raw,D(w),-1)
        else:raise ValueError('Invalid kind')
        if any(len(w)!=5 or w[0]==0 or w[-1]==-1 for w in raw):
            raise ValueError('Invalid resulting word')
        add(R,antisym(raw),-Q(row['coefficient']))
    if R:raise ArithmeticError(f'{len(R)} surviving full-word coefficients')
    return {'result':'PASS','method':'independent placement/merge enumeration',
            'projection':'full antisymmetrization, not compressed coordinates',
            'nonzero_residual_coordinates':0,'rows':len(data['rows'])}

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',nargs='?',type=Path,
                    default=Path(__file__).resolve().parents[1]/'data/S4_certificate.json')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    text=json.dumps(verify(args.certificate),indent=2)+'\n'
    print(text,end='')
    if args.receipt:args.receipt.write_text(text)
