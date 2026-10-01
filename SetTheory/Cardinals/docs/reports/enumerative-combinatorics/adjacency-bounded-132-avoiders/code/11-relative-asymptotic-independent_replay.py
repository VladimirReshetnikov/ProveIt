"""Independent permutation-level replay of the relaxed envelope grammar.
No imports from the author's verifier or counting implementation.
"""
from functools import cache
from fractions import Fraction
from math import comb
from collections import Counter

MAXN=10
@cache
def av(n):
    if not n:return ((),)
    out=[]
    for l in range(n):
        r=n-1-l
        for a in av(l):
            for b in av(r):out.append(tuple(x+r for x in a)+(n,)+b)
    return tuple(out)

def parse(p,M):
    """Returns decoration deficiencies and maximal append-run lengths."""
    ds=[];runs=[];run=0
    while len(p)>1:
        n=len(p);j=p.index(n)
        if j==n-1:
            if n-1-p[-2]>M-1:return None
            run+=1;p=p[:-1]
        else:
            if j+1>M:return None
            if run:runs.append(run);run=0
            # The standard maximum decomposition shifts the left decoration.
            ds.append(n-p[0] if j else 0)
            p=p[j+1:]
    if run:runs.append(run)
    return ds,runs

def envelope(M,n):
    k=[0]+[comb(2*(i-1),i-1)//i for i in range(1,M+1)]
    u=[1]+[0]*n
    for j in range(1,n+1):u[j]=sum(k[i]*u[j-i] for i in range(1,min(M,j)+1))
    return [0]+[sum(u[j]*u[v-1-j] for j in range(v)) for v in range(1,n+1)]

shape_checks=good_checks=bad_checks=0
for M in range(1,6):
    E=envelope(M,MAXN)
    for n in range(1,MAXN+1):
        objs=[(p,parse(p,M)) for p in av(n)]
        objs=[(p,v) for p,v in objs if v is not None]
        if len(objs)!=E[n]:raise RuntimeError(('envelope',M,n,len(objs),E[n]))
        shape_checks+=1
        for D in range(1,4):
            eps=Fraction(D+2,2**D)
            bad=sum(any(x>D for x in v[0]) for _,v in objs)
            if bad>n*eps*E[n]:raise RuntimeError(('decoration',M,n,D,bad,E[n]))
            for L in range(1,4):
                badrun=sum(any(x>L for x in v[1]) for _,v in objs)
                if n>L and badrun>n*E[n-L]:raise RuntimeError(('append',M,n,L,badrun,E[n-L]))
                bad_checks+=1
                m=M+D+L
                for p,v in objs:
                    if any(x>D for x in v[0]) or any(x>L for x in v[1]):continue
                    if any(abs(a-b)>m for a,b in zip(p,p[1:])):raise RuntimeError(('notcap',M,n,D,L,p,v))
                    good_checks+=1
print({'max_n':MAXN,'envelope_equalities':shape_checks,'bad_family_parameter_checks':bad_checks,'good_object_cap_checks':good_checks})
