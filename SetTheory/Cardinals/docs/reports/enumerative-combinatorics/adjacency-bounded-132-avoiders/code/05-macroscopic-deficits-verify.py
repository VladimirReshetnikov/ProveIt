"""Finite checks, not a proof-assistant verification of the asymptotic theorems.
Run without Python's -O option: the verification deliberately uses assertions.
"""
from __future__ import annotations
from collections import Counter as Histogram
from functools import lru_cache
from math import comb
import json, pathlib
from model import Counter, av, mx, catalans
ROOT=pathlib.Path(__file__).resolve().parents[1]

def standardize(p: tuple[int,...]) -> tuple[int,...]:
    order={x:i+1 for i,x in enumerate(sorted(p))}
    return tuple(order[x] for x in p)

def parse(p: tuple[int,...],m:int):
    """Return the canonical outer word, its cost and the terminal blocks."""
    word=[];t=0;core=p
    while True:
        n=len(core);j=core.index(n)
        a=standardize(core[:j]);b=standardize(core[j+1:])
        if len(a)<=m and len(b)<=m:return tuple(word),t,a,b
        if len(b)>m:
            word.append(('R',a));t+=len(a)+1;core=b
        else:
            assert len(a)>m and len(b)==0
            word.append(('A',()));t+=1;core=a

def reconstruct(word,a,b):
    core=tuple(x+len(b) for x in a)+(len(a)+len(b)+1,)+b
    for kind,dec in reversed(word):
        if kind=='A':core=core+(len(core)+1,)
        else:core=tuple(x+len(core) for x in dec)+(len(core)+len(dec)+1,)+core
    return core

def main():
    permutations=0;count_tests=0;endpoint_tests=0;parser_tests=0
    for n in range(2,10):
        ps=av(n);permutations+=len(ps)
        assert len(ps)==comb(2*n,n)//(n+1)
        hist=Histogram(mx(p) for p in ps)
        for m in range(1,n):
            obj=Counter(n,m)
            assert obj.count()==sum(c for v,c in hist.items() if v<=m)
            count_tests+=1
            if n<=7:
                exact=[[0]*n for _ in range(n)]
                for p in ps:
                    if mx(p)<=m:exact[n-p[0]][n-p[-1]]+=1
                for u in range(n):
                    for v in range(n):
                        wanted=sum(exact[i][j] for i in range(u+1) for j in range(v+1))
                        assert obj.T(n,u,v)==wanted,(n,m,u,v)
                        endpoint_tests+=1
        for p in ps:
            for m in range((n+1)//2,n):
                if mx(p)>m:continue
                w,t,a,b=parse(p,m)
                assert 0<=t<=n-m-1
                assert len(a)+len(b)+1==n-t>m
                assert len(a)<=m and len(b)<=m
                assert reconstruct(w,a,b)==p
                parser_tests+=1
        for f in range(1,n+1):
            wanted=sum(p[0]==f for p in ps)
            assert wanted==(n-f+1)*comb(n+f-2,n-1)//n
        C=catalans(n)
        for ell in range(1,n+1):
            assert sum(p[-1]==ell for p in ps)==C[n-ell]*C[ell-1]
    C=catalans(62);w=[1];r=[1]
    for t in range(1,61):
        w.append(w[-1]+sum(C[k-1]*w[t-k] for k in range(1,t+1)))
        r.append(sum(C[k-1]*r[t-k] for k in range(1,t+1)))
        assert w[t]==C[t+1]
        assert r[t]==C[t]
    report={'status':'PASS','max_exhaustive_n':9,'permutations_checked':permutations,
        'total_count_checks':count_tests,'endpoint_state_checks':endpoint_tests,
        'canonical_parser_checks':parser_tests,'word_coefficients_checked':60,
        'formal_verification':False,
        'scope':'Exact finite identities only; analytic proofs are in article.tex.'}
    (ROOT/'data/verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
