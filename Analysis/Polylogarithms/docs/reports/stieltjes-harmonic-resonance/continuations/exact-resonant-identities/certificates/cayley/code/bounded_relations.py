#!/usr/bin/env python3
"""Independent exact S6 proof-search obstruction verifier.

Placement shuffle and stack-merge stuffle primitives are adapted from the
existing Cayley S4 independent verifier supplied with ProveIt. This file
does not import the exploratory matrix generator or any arithmetic library.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json
from math import gcd


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

def plus(a,b,factor=1):
    out=defaultdict(int);add(out,a);add(out,b,factor)
    return {w:c for w,c in out.items() if c}

def product_poly(a,b):
    out=defaultdict(int)
    for u,x in a.items():
        for v,y in b.items():add(out,stuffleword(u,v),x*y)
    return dict(out)

def single(w,c):return {(-1,)*(w-1)+(c,):1}

def rel2():
    out={(-1,1,3):1,(-1,1,1):3}
    out=plus(out,single(3,1),-1)
    return plus(out,product_poly(single(2,1),single(1,2)),-2)

def rel4():
    out={(-1,-1,-1,1,3):35,(-1,-1,-1,1,1):-255,(-1,-1,1,-1,1):-120}
    out=plus(out,single(5,1),-57)
    return plus(out,product_poly(single(4,1),single(1,2)),-70)

def expand(w):
    table={'z':[(-1,1)],'x':[(0,1),(2,-1)],'y':[(1,1),(3,-1)],
           'b':[(2,1)],'h':[(1,1),(3,1),(2,-1)]}
    out=defaultdict(int)
    for choice in product(*(table[a] for a in w)):
        c=1
        for k,m in choice:c*=m
        out[tuple(k for k,m in choice)]+=c
    return {w:c for w,c in out.items() if c}

def rowof(desc):
    kind=desc[0]
    if kind=='DS':
        u,v=map(tuple,desc[1:])
        assert (u==(0,) or (u[0]!=0 and u[-1]!=-1)) and v[0]!=0 and v[-1]!=-1
        assert sum(a!=-1 for a in u+v)<=4
        return plus(sh(u,v),stuffleword(u,v),-1)
    if kind=='DIST':
        ind=[tuple(z) for z in desc[1]];v=tuple(desc[2]);weight=sum(a for a,c in ind)
        assert all(c in (0,1) for a,c in ind)
        doubled=wordof([(a,2*c) for a,c in ind])
        assert doubled[0]!=0
        row={doubled:1}
        for eps in product((0,2),repeat=len(ind)):
            w=wordof([(a,(c+e)%4) for (a,c),e in zip(ind,eps)])
            assert w[0]!=0
            row=plus(row,{w:1},-2**(weight-len(ind)))
        return product_poly(row,{v:1}) if v else row
    if kind=='LIFT':
        k=desc[1];v=tuple(desc[2]);assert k in (3,5)
        row=antisym(rel2() if k==3 else rel4())
        return product_poly(row,plus({v:1},{conjugation(v):1}))
    if kind=='CAYLEY_BALANCED_LIFT':
        w=tuple(desc[1]);v=tuple(desc[2]);assert w[0]!='x' and w[-1]!='z'
        original=expand(w)
        # Use the raw five-letter Cayley substitution rather than the
        # symbolic z<->x eigenvector shortcut used in discovery.
        transformed=defaultdict(int)
        for u,c in original.items():add(transformed,D(u),c)
        row=plus(original,transformed,-1)
        return product_poly(row,{v:1}) if v else row
    raise ValueError(kind)

def target():
    out={(-1,-1,-1,-1,-1,1,3):128588,
         (-1,-1,-1,-1,-1,1,1):3138084,
         (-1,-1,-1,-1,1,-1,1):1592832,
         (-1,-1,-1,1,-1,-1,1):521184}
    out=plus(out,single(7,1),-216172)
    out=plus(out,product_poly(single(4,1),single(3,0)),48861)
    return plus(out,product_poly(single(6,1),single(1,2)),-257176)

def compress(row):
    out=defaultdict(int)
    for w,c in row.items():
        v=conjugation(w)
        if w<v:out[w]+=c
        elif v<w:out[v]-=c
    return {w:c for w,c in out.items() if c}

def canonical(row):
    row=compress(row)
    if not row:return ()
    divisor=0
    for c in row.values():divisor=gcd(divisor,c)
    if row[min(row)]<0:divisor=-divisor
    return tuple(sorted((w,c//divisor) for w,c in row.items()))

def complete_family():
    # Re-enumerate the whole prescribed family independently of the stored
    # descriptors, using raw words rather than the discovery code's
    # recursive weight/color compositions.
    byweight={0:[()]}
    for weight in range(1,7):
        byweight[weight]=[w for w in product(range(-1,4),repeat=weight)
                          if w[0]!=0 and w[-1]!=-1
                          and sum(a!=-1 for a in w)<=4]
    def admissible_at(weight,depth):
        return [w for w in byweight[weight] if sum(a!=-1 for a in w)<=depth]
    result=set();counts={}
    def insert(desc):
        key=canonical(rowof(desc))
        if key:result.add(key)
    for weight in range(1,4):
        left=byweight[weight]+([(0,)] if weight==1 else [])
        for u in left:
            for v in byweight[7-weight]:
                if sum(a!=-1 for a in u+v)<=4:insert(['DS',u,v])
    counts['DS']=len(result)
    for weight in range(1,8):
        for depth in range(1,min(weight,4)+1):
            for cuts in combinations(range(1,weight),depth-1):
                edges=(0,)+cuts+(weight,)
                exponents=tuple(edges[j+1]-edges[j] for j in range(depth))
                for colors in product((0,1),repeat=depth):
                    if exponents[0]==1 and colors[0]==0:continue
                    ind=list(zip(exponents,colors))
                    for v in admissible_at(7-weight,4-depth):insert(['DIST',ind,v])
    counts['DIST']=len(result)-sum(counts.values())
    for weight in (3,5):
        for v in admissible_at(7-weight,2):insert(['LIFT',weight,v])
    counts['LIFT']=len(result)-sum(counts.values())
    for weight in range(1,8):
        for w in product('zxbyh',repeat=weight):
            if w[0]=='x' or w[-1]=='z':continue
            common=min(w.count('z'),w.count('x'))
            if common<1:continue
            seed_depth=weight-common
            if seed_depth>4 or (weight<7 and seed_depth==4):continue
            for v in admissible_at(7-weight,4-seed_depth):
                insert(['CAYLEY_BALANCED_LIFT',w,v])
    counts['CAYLEY_BALANCED_LIFT']=len(result)-sum(counts.values())
    return result,counts

def verify(path):
    data=json.loads(path.read_text())
    coords=[tuple(w) for w in data['coordinates']]
    assert len(coords)==len(set(coords))==2546
    ell={coords[i]:v for i,v in data['functional']}
    assert len(ell)>0
    assert all(w<conjugation(w) for w in ell)
    def pair(row):return sum(c*ell.get(w,0) for w,c in compress(row).items())
    counts=defaultdict(int);max_support=0;stored_family=set()
    for d in data['row_descriptors']:
        row=rowof(d)
        assert all(len(w)==7 and w[0]!=0 and w[-1]!=-1 for w in row)
        assert all(sum(a!=-1 for a in w)<=4 for w in row)
        assert pair(row)==0,d
        counts[d[0]]+=1;max_support=max(max_support,len(row));stored_family.add(canonical(row))
    regenerated,full_counts=complete_family()
    assert regenerated==stored_family
    assert dict(counts)==full_counts
    expected={coords[i]:c for i,c in data['target']}
    assert compress(target())==expected
    pairing=pair(target());assert pairing==data['pairing'] and pairing!=0
    return {'result':'PASS','rows_verified':len(data['row_descriptors']),
            'row_type_counts':dict(counts),'ambient_coordinates':len(coords),
            'functional_support':len(ell),'target_pairing':str(pairing),
            'largest_row_support':max_support,'complete_family_reenumeration':'PASS',
            'arithmetic':'integers only; no rank computation, PSLQ, modular arithmetic, or floating-point values',
            'scope':'nonmembership in the explicitly specified finite relation span; S6 remains conjectural'}

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,
                        default=Path(__file__).resolve().parents[2]/'results/s6/S6_depth_bounded_separator.json')
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args();receipt=verify(args.certificate)
    result=json.dumps(receipt,indent=2)+'\n';print(result,end='')
    if args.receipt:args.receipt.write_text(result)
