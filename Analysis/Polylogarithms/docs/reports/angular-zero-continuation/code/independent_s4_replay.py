#!/usr/bin/env python3
"""Independent exact replay; does not import the search or its verifier.

Shuffle uses subsets of positions rather than recursive first-letter shuffling.
Stuffle is positive in Li conventions; depth signs are applied on conversion.
"""
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import json

A=(-2,-1,0,1,2)
expo={1:0,2:1,-1:2,-2:3}
root={e:a for a,e in expo.items()}

def plus(out,k,c):
    out[k]+=c
    if out[k]==0: del out[k]

@lru_cache(None)
def shuffle(u,v):
    ans=defaultdict(int); n=len(u)+len(v)
    for positions in combinations(range(n),len(u)):
        pos=set(positions);i=j=0;w=[]
        for k in range(n):
            if k in pos:w.append(u[i]);i+=1
            else:w.append(v[j]);j+=1
        ans[tuple(w)]+=1
    return dict(ans)

def word_to_li(u):
    prev=0;s=1;out=[]
    for a in u:
        if a==0:s+=1
        else:
            e=expo[a];out.append((s,(prev-e)%4));prev=e;s=1
    assert s==1
    return tuple(out)

def li_to_word(u):
    e=0;out=[]
    for s,x in u:
        e=(e-x)%4;out.extend([0]*(s-1));out.append(root[e])
    return tuple(out)

@lru_cache(None)
def positive_stuffle(u,v):
    if not u:return {v:1}
    if not v:return {u:1}
    out=defaultdict(int)
    for t,c in positive_stuffle(u[1:],v).items():out[(u[0],)+t]+=c
    for t,c in positive_stuffle(u,v[1:]).items():out[(v[0],)+t]+=c
    h=(u[0][0]+v[0][0],(u[0][1]+v[0][1])%4)
    for t,c in positive_stuffle(u[1:],v[1:]).items():out[(h,)+t]+=c
    return dict(out)

def double_shuffle(u,v):
    def admissible(z):
        return bool(z) and z[0]!=1 and z[-1]!=0 and all(a in A for a in z)
    assert ((admissible(u) and admissible(v)) or
            (u==(1,) and admissible(v)) or
            (v==(1,) and admissible(u)))
    x=word_to_li(u);y=word_to_li(v);out=defaultdict(int)
    for z,c in positive_stuffle(x,y).items():
        plus(out,li_to_word(z),(-1)**(len(x)+len(y)+len(z))*c)
    for z,c in shuffle(u,v).items():plus(out,z,-c)
    assert all(z[0]!=1 and z[-1]!=0 for z in out)
    return out

pull={0:((1,1),(-1,-1)),1:((0,1),(-1,-1)),
      -1:((-1,-1),),2:((-2,1),(-1,-1)),-2:((2,1),(-1,-1))}

def octahedral(u):
    assert u and u[0]!=1 and u[-1]!=0 and all(a in A for a in u)
    out=defaultdict(int);out[u]=1
    for factors in product(*(pull[a] for a in u[::-1])):
        z=tuple(a for a,c in factors); c=-(-1)**len(u)
        for a,d in factors:c*=d
        plus(out,z,c)
    assert all(z[0]!=1 and z[-1]!=0 for z in out)
    return out

def imaginary(row):
    out=defaultdict(int)
    for u,c in row.items():
        v=tuple(-a if a in (-2,2) else a for a in u)
        if u<v:plus(out,u,c)
        elif u>v:plus(out,v,-c)
    return out

def independently_form_target(weight):
    out=defaultdict(int)
    from math import factorial
    if weight==3:
        out[(0,-2,-2)]=12
        out[(0,-2,2)]=4
        for z in product((2,-2),repeat=3):
            plus(out,z,factorial(3)*(-1)**z.count(-2))
        for z,c in shuffle((0,-2),(-1,)).items():plus(out,z,-8*c)
        return imaginary(out)
    assert weight==5
    for z,c in [((0,0,0,-2,-2),96),((0,0,-2,0,-2),96),
                ((0,-2,0,0,-2),288),((0,0,0,-2,2),224)]:out[z]=c
    # P^5, P=H(i)-H(-i). Five singleton shuffles give 5! per word.
    for z in product((2,-2),repeat=5):
        plus(out,z,-32*factorial(5)*(-1)**z.count(-2))
    for z,c in shuffle((0,0,0,-2),(-1,)).items():plus(out,z,-448*c)
    for z,c in shuffle((0,-2),(0,0,1)).items():plus(out,z,27*c)
    return imaginary(out)

def verify(weight):
    filename={3:'s2_exact_certificate.json',5:'s4_exact_certificate.json'}[weight]
    p=Path(__file__).resolve().parent.parent/'data'/filename
    cert=json.loads(p.read_text());total=defaultdict(Fraction);counts=defaultdict(int)
    for item in cert['rows']:
        lab=item['label'];kind=lab[0]
        if kind=='ds':
            assert len(lab[1])+len(lab[2])==weight
            row=double_shuffle(tuple(lab[1]),tuple(lab[2]))
        elif kind=='octa':
            assert len(lab[1])==weight
            row=octahedral(tuple(lab[1]))
        else:raise ValueError(kind)
        c=Fraction(item['coefficient'])
        for z,a in imaginary(row).items():plus(total,z,c*a)
        counts[kind]+=1
    expected=independently_form_target(weight)
    assert dict(total)==dict(expected)
    if weight==5:assert len(cert['coordinates'])==946
    receipt={'pass':True,'independent_generator_replay':True,
                      'weight':weight,
                      'relations':dict(counts),'target_support':len(expected),
                      'arithmetic':'exact Python integers and fractions'}
    print(json.dumps(receipt,indent=2))
    return receipt

if __name__=='__main__':
    verify(3)
    verify(5)
