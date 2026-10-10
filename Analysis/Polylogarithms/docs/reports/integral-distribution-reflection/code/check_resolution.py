#!/usr/bin/env python3
"""Direct finite-field checks of the weighted Anderson resolution.

Assembles the complex from rational grid labels, without using a normal
form. Also checks that a non-fixed source never has a fixed target term.
"""
from itertools import combinations, product
from pathlib import Path
import math
import json
ROOT=Path(__file__).resolve().parents[1]

if not __debug__:
    raise RuntimeError('Run without -O: exact validation uses assertions.')


def prime_list(q):
    return [p for p in range(2,q+1) if q%p==0 and all(p%t for t in range(2,math.isqrt(p)+1))]

def rank_columns(cols,mod):
    piv={}
    for raw in cols:
        v={i:c%mod for i,c in raw.items() if c%mod}
        while v:
            p=min(v)
            if p not in piv:
                inv=pow(v[p],-1,mod)
                piv[p]={i:c*inv%mod for i,c in v.items()}
                break
            a=v[p]
            for i,c in piv[p].items():
                z=(v.get(i,0)-a*c)%mod
                if z:v[i]=z
                elif i in v:del v[i]
    return len(piv)

def build(q,w):
    ps=prime_list(q);cells=[]
    for k in range(len(ps)+1):
        cells.append([(S,a) for S in combinations(ps,k)
                      for a in range(0,q,math.prod(S))])
    maps=[None]
    for k in range(1,len(cells)):
        ix={cell:i for i,cell in enumerate(cells[k-1])};cols=[]
        for S,a in cells[k]:
            v={};d=math.prod(S);m=q//d
            def add(i,c):
                z=v.get(i,0)+c
                if z:v[i]=z
                elif i in v:del v[i]
            for h,p in enumerate(S):
                T=tuple(t for t in S if t!=p);sign=(-1)**h
                for j in range(p):
                    b=(d//p)*(a//d+j*m)
                    add(ix[T,b],sign)
                add(ix[T,a],-sign*w[p])
            if 2*a%q:
                assert all(2*cells[k-1][i][1]%q for i in v)
            cols.append(v)
        maps.append(cols)
    for k in range(2,len(cells)):
        for v in maps[k]:
            out={}
            for i,c in v.items():
                for j,b in maps[k-1][i].items():out[j]=out.get(j,0)+c*b
            assert all(z==0 for z in out.values())
    return cells,maps

def main():
    cases=[]
    for q in list(range(2,41))+[60,72,105,120,210]:
        ps=prime_list(q)
        for vals in product([0,1],repeat=len(ps)):
            w=dict(zip(ps,vals));cells,maps=build(q,w)
            for mod in [2,3,5]:
                ranks=[0]+[rank_columns(maps[k],mod) for k in range(1,len(cells))]+[0]
                hom=[len(cells[k])-ranks[k]-ranks[k+1] for k in range(len(cells))]
                assert hom[0]==sum(math.gcd(a,q)==1 for a in range(q)) and not any(hom[1:])
                cases.append(dict(q=q,weights=w,modulus=mod,
                                  dimensions=[len(c) for c in cells],ranks=ranks[1:-1],homology=hom))
    result=dict(case_count=len(cases), all_d_squared_zero=True,
                nonfixed_support_preserved=True, all_negative_homology_zero=True,cases=cases)
    (ROOT/'data'/'resolution_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
if __name__=='__main__': main()
