"""Sparse polynomial/Laurent-polynomial arithmetic over exact integers or rationals."""
from collections import defaultdict
from math import comb

def clean(p):return {m:c for m,c in p.items() if c}
def mon(m,c=1):return {tuple(m):c} if c else {}
def add(*args):
    z=defaultdict(int)
    for p in args:
        for m,c in p.items():z[m]+=c
    return clean(z)
def scale(p,c):return clean({m:c*v for m,v in p.items()})
def sub(p,q):return add(p,scale(q,-1))
def mul(p,q):
    z=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():z[tuple(x+y for x,y in zip(m,n))]+=c*d
    return clean(z)
def power(p,n):
    z=mon((0,)*len(next(iter(p))))
    while n:
        if n&1:z=mul(z,p)
        n//=2
        if n:p=mul(p,p)
    return z
def shift(p,offsets):
    for j,b in enumerate(offsets):
        if not b:continue
        q=defaultdict(int)
        for m,c in p.items():
            if m[j]<0:raise ValueError('cannot shift negative exponent')
            for k in range(m[j]+1):
                n=list(m);n[j]=k
                q[tuple(n)]+=c*comb(m[j],k)*b**(m[j]-k)
        p=clean(q)
    return p
def weight(p,w):return max(sum(x*y for x,y in zip(m,w)) for m in p)
def value(p,values,mod):
    z=0
    for m,c in p.items():
        t=c
        for x,e in zip(values,m):t=t*pow(x,e,mod)%mod
        z=(z+t)%mod
    return z
