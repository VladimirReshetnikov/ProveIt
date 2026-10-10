"""Exact word relations at level four, for an S4 proof search.

H(a1,...,aw) uses dt/(t-a), outer letter first, endpoint 1.
The coding 2=i and -2=-i is used.  Every nonempty coordinate is convergent.
Relations are represented before numerical evaluation, over the integers.
"""
from functools import lru_cache
from collections import Counter
from itertools import product
import json
from pathlib import Path
from package_io import write_json_new_or_compare

ALPH=(-2,-1,0,1,2)
NZ=(-2,-1,1,2)
TO_EXP={1:0,2:1,-1:2,-2:3}
FROM_EXP={v:k for k,v in TO_EXP.items()}

def admissible(u):
    return bool(u) and u[0]!=1 and u[-1]!=0 and all(a in ALPH for a in u)

@lru_cache(None)
def words(w):
    if w==0:return ((),)
    return tuple(t for t in product(ALPH,repeat=w) if t[0]!=1 and t[-1]!=0)

def add(d,k,v):
    d[k]+=v
    if not d[k]:del d[k]

@lru_cache(None)
def sh(u,v):
    if not u:return {v:1}
    if not v:return {u:1}
    ans=Counter()
    for t,c in sh(u[1:],v).items():add(ans,(u[0],)+t,c)
    for t,c in sh(u,v[1:]).items():add(ans,(v[0],)+t,c)
    return dict(ans)

def shuffle_lin(a,b):
    ans=Counter()
    for u,cu in a.items():
        for v,cv in b.items():
            for t,c in sh(u,v).items():add(ans,t,cu*cv*c)
    return ans

def sub(a,b):
    c=Counter(a)
    for k,v in b.items():add(c,k,-v)
    return c

def scalar(a,c):return {k:c*v for k,v in a.items() if c*v}

@lru_cache(None)
def h_to_li(u):
    out=[];s=1;prev=0
    for a in u:
        if a==0:s+=1
        else:
            e=TO_EXP[a]
            out.append((s,(prev-e)%4));prev=e;s=1
    assert s==1
    return tuple(out)

@lru_cache(None)
def li_to_h(u):
    out=[];prev=0
    for s,c in u:
        prev=(prev-c)%4
        out.extend((0,)*(s-1));out.append(FROM_EXP[prev])
    return tuple(out)

@lru_cache(None)
def st(u,v):
    if not u:return {v:1}
    if not v:return {u:1}
    ans=Counter()
    for t,c in st(u[1:],v).items():add(ans,(u[0],)+t,c)
    for t,c in st(u,v[1:]).items():add(ans,(v[0],)+t,c)
    merged=(u[0][0]+v[0][0],(u[0][1]+v[0][1])%4)
    for t,c in st(u[1:],v[1:]).items():add(ans,(merged,)+t,-c)
    return dict(ans)

@lru_cache(None)
def ds(u,v):
    assert ((admissible(u) and admissible(v)) or
            (u==(1,) and admissible(v)) or
            (v==(1,) and admissible(u))), 'Only finite or degree-one regularized products are allowed'
    stu={li_to_h(t):c for t,c in st(h_to_li(u),h_to_li(v)).items()}
    ans=sub(stu,sh(u,v))
    assert all(w[0]!=1 and w[-1]!=0 for w in ans)
    return dict(ans)

PULL={0:{1:1,-1:-1},1:{0:1,-1:-1},-1:{-1:-1},2:{-2:1,-1:-1},-2:{2:1,-1:-1}}

@lru_cache(None)
def octa(u):
    assert admissible(u), 'Octahedral inputs must be termwise endpoint-admissible'
    ans={():1}
    for a in reversed(u):
        new=Counter()
        for t,c in ans.items():
            for b,d in PULL[a].items():add(new,t+(b,),c*d)
        ans=new
    ans=sub({u:1},scalar(ans,(-1)**len(u)))
    assert all(w[0]!=1 and w[-1]!=0 for w in ans)
    return dict(ans)

def conj(u):return tuple(-a if abs(a)==2 else a for a in u)

def imag(row):
    ans=Counter()
    for u,c in row.items():
        v=conj(u)
        if u<v:add(ans,u,c)
        elif u>v:add(ans,v,-c)
    return ans

def coords(w):return tuple(u for u in words(w) if u<conj(u))

def basic(w,oct=True):
    for a in range(1,w//2+1):
        b=w-a
        for u in words(a):
            for v in words(b):
                if a==b and u>v:continue
                yield ['ds',u,v],ds(u,v)
    for v in words(w-1):
        yield ['ds',(1,),v],ds((1,),v)
    if oct:
        for u in words(w):yield ['octa',u],octa(u)

LOGREL={(2,):1,(-2,):1,(-1,):-1}

def target():
    T=Counter({(0,0,0,-2,-2):3,(0,0,-2,0,-2):3,(0,-2,0,0,-2):9,(0,0,0,-2,2):7})
    P={(2,):1,(-2,):-1};P5={():1}
    for j in range(5):P5=shuffle_lin(P5,P)
    T=sub(T,P5)
    T=scalar(T,32)
    T=sub(T,scalar(sh((0,0,0,-2),(-1,)),32*14))
    T=sub(T,scalar(sh((0,-2),(0,0,1)),-27))
    return imag(T)

def row_stream(w=5):
    yield from basic(w)
    for v in words(w-1):yield ['lift-log',v],shuffle_lin(LOGREL,{v:1})
    for k in range(2,w):
        for tag,row in basic(k):
            if not row:continue
            for v in words(w-k):
                yield ['lift',tag,v],shuffle_lin(row,{v:1})

def dump(destination):
    keys=coords(5);idx={k:i for i,k in enumerate(keys)}
    rows=[];labels=[];seen=set()
    for tag,row in row_stream():
        row=imag(row)
        if not row:continue
        out=tuple(sorted((idx[k],v) for k,v in row.items()))
        if out in seen:continue
        seen.add(out);rows.append(out);labels.append(tag)
    obj={'keys':keys,'rows':rows,'labels':labels,'target':[(idx[k],v) for k,v in target().items()]}
    p=Path(destination);write_json_new_or_compare(p,obj)
    print('system',len(rows),'x',len(keys),'saved',p)
    return obj

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dump',type=Path,required=True,help='Explicit destination for the optional search matrix')
    args=parser.parse_args()
    dump(args.dump)
