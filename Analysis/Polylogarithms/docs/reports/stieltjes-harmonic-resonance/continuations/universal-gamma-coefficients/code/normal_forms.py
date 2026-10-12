"""Independent exact integration-by-parts normalizer using Fraction dictionaries.

No closed coefficient formulas are used in this module.
"""
from functools import lru_cache
from fractions import Fraction as Q
from collections import defaultdict

def trim(m):
    m=list(m)
    while m and m[-1]==0:m.pop()
    return tuple(m)
def addto(P,m,c):
    if c:
        P[m]=P.get(m,Q(0))+c
        if not P[m]:del P[m]
def Dmon(m):
    R={}
    for j,a in enumerate(m):
        if a:
            n=list(m)+[0];n[j]-=1;n[j+1]+=1;addto(R,trim(n),Q(a))
    return R
def D(P):
    R={}
    for m,c in P.items():
        for n,d in Dmon(m).items():addto(R,n,c*d)
    return R
@lru_cache(None)
def NH(m):
    if len(m)<=1 or m[-1]>=2:return {m:Q(1)},{}
    r=len(m)-1;T=list(m);T[r]-=1;T[r-1]+=1;a=T[r-1];T=trim(T)
    R=Dmon(T);assert R.pop(m)==a
    N={};H={T:Q(1,a)}
    for n,d in R.items():
        nn,hh=NH(n)
        for x,c in nn.items():addto(N,x,-d*c/a)
        for x,c in hh.items():addto(H,x,-d*c/a)
    return N,H

def normal(P):
    N={};H={}
    for m,c in P.items():
        nn,hh=NH(m)
        for x,d in nn.items():addto(N,x,c*d)
        for x,d in hh.items():addto(H,x,c*d)
    return N,H

def hierarchy(M):
    A={():Q(1)}
    for m in range(M+1):
        N,H=normal(A);yield m,A,N,H
        B={}
        for k,c in A.items():
            j=list(k or (0,));j[0]+=1;addto(B,tuple(j),c)
        for k,c in D(A).items():addto(B,k,-c)
        A=B

def sympy(P):
    import sympy as s
    return s.Add(*[s.Rational(c.numerator,c.denominator)*s.Mul(*[s.Symbol(f'u_{i}')**a for i,a in enumerate(m) if a]) for m,c in P.items()])
if __name__=='__main__':
    import time,json
    start=time.time();out={}
    for m,A,N,H in hierarchy(18):
        V=D(H)
        for k,c in N.items():addto(V,k,c)
        assert V==A
        print(m,len(A),len(N),len(H),flush=True)
        if m in [8,11,14]:print('N=',sympy(N),flush=True)
        out[str(m)]={'A':[{'powers':k,'coefficient':str(v)} for k,v in A.items()], 'N':[{'powers':k,'coefficient':str(v)} for k,v in N.items()], 'H':[{'powers':k,'coefficient':str(v)} for k,v in H.items()]}
    open(__import__('pathlib').Path(__file__).resolve().parents[1]/'data'/'normal_forms_through_18.json','w').write(json.dumps(out,indent=2))
    print('time',time.time()-start)
