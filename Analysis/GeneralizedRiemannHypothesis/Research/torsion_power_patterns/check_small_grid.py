#!/usr/bin/env python3
"""Exact finite multidimensional obstruction cost for p=2, h0=3, H=3, s=2.
K=Q_2(zeta_8). Work in Q[X]/(X^4+1); t=X-1 is a uniformizer.
Column elimination over its valuation ring computes a basis for every evaluation kernel.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb

E=4
Z=(Q(0),)*E
O=(Q(1),)+(Q(0),)*(E-1)
X=(Q(0),Q(1),Q(0),Q(0))

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
@lru_cache(maxsize=200000)
def mul(a,b):
    if a==Z or b==Z:return Z
    c=[Q(0)]*E
    for i,x in enumerate(a):
        if not x:continue
        for j,y in enumerate(b):
            if y:
                k=i+j
                c[k%E]+=x*y*(1 if k<E else -1)
    return tuple(c)

def powr(a,k):
    b=O
    for _ in range(k):b=mul(b,a)
    return b

def v2q(x):
    if not x:return float('inf')
    def v(n):return (abs(n)&-abs(n)).bit_length()-1
    return v(x.numerator)-v(x.denominator)

@lru_cache(maxsize=200000)
def val(a):
    if a==Z:return float('inf')
    # Expand in t=X-1. Distinct residues of the valuations modulo 1
    # make the minimum exact by Eisenstein's criterion.
    return min(v2q(sum((a[k]*comb(k,i) for k in range(i,E)),Q(0)))+Q(i,E) for i in range(E))

@lru_cache(maxsize=100000)
def inv(a):
    assert a!=Z
    # solve a*b=1 over Q by exact elimination
    m=[list(row)+[O[i]] for i,row in enumerate(zip(*(mul(a,tuple(Q(k==j) for k in range(E))) for j in range(E))))]
    for j in range(E):
        k=next(i for i in range(j,E) if m[i][j]);m[j],m[k]=m[k],m[j]
        q=m[j][j];m[j]=[x/q for x in m[j]]
        for i in range(E):
            if i==j:continue
            q=m[i][j]
            if q:m[i]=[x-q*y for x,y in zip(m[i],m[j])]
    b=tuple(row[-1] for row in m);assert mul(a,b)==O
    return b

def lincomb(a,c,b):
    if c==Z:return a
    out=dict(a)
    for k,x in b.items():
        out[k]=sub(out.get(k,Z),mul(c,x))
        if out[k]==Z:del out[k]
    return out


def min_kernel_cost(D,mons,evaluations,r):
    # Each basis column records its polynomial and its evaluations.
    # Pivot with least valuation, so every multiplier is integral.
    cols=[({a:O},[evaluations[z][j] for z in D]) for j,a in enumerate(mons)]
    m=len(D)
    while m:
        candidates=[(val(x),j,i) for j,(_,es) in enumerate(cols) for i,x in enumerate(es) if x!=Z]
        if not candidates:break
        _,j,i=min(candidates)
        P,ev=cols.pop(j); ip=inv(ev[i])
        new=[]
        for R,fs in cols:
            c=mul(fs[i],ip);assert val(c)>=0
            S=lincomb(R,c,P)
            gs=[sub(f,mul(c,e)) for k,(f,e) in enumerate(zip(fs,ev)) if k!=i]
            new.append((S,gs))
        cols=new;m-=1
    if not cols:return float('inf'),None
    result=min((min(val(c)+r*sum(a) for a,c in R.items()),j) for j,(R,_) in enumerate(cols))
    cost,j=result
    P=cols[j][0]
    assert all(sum_field(mul(c,evaluations[z][mons.index(a)]) for a,c in P.items())==Z for z in D)
    return cost,P


def sum_field(vs):
    s=Z
    for v in vs:s=add(s,v)
    return s


def main():
    # input exact order 8, parent exact order 4. Each parent tuple has four children.
    # A minimal cover of the disjoint stars chooses the parent or every child.
    A=(1,3,5,7);parents=list(product((2,6),repeat=2));children={z:[w for w in product(A,repeat=2) if tuple(2*a%8 for a in w)==z] for z in parents}
    V=list(product((1,2,3,5,6,7),repeat=2));d=6;r=Q(1,2)
    mons=list(product(range(d),repeat=2))
    powers={a:[powr(sub(powr(X,a),O),k) for k in range(d)] for a in (1,2,3,5,6,7)}
    ev={z:[mul(powers[z[0]][a],powers[z[1]][b]) for a,b in mons] for z in V}
    best=Q(2);best_data=None
    for bits in product((0,1),repeat=len(parents)):
        D=[w for z,b in zip(parents,bits) for w in ([z] if b else children[z])]
        cost,P=min_kernel_cost(D,mons,ev,r)
        # g(T_1) has cost 2, covers all outputs.
        print('parents selected',''.join(map(str,bits)),'nodes',len(D),'min cost',cost)
        if cost<best:best=cost;best_data=(D,P)
    print('exact cost:',best)
    assert best==1,(best,best_data)
    print('All 16 minimal star covers certified. C_2({3},{1,2})=1 at r=1/2.')

if __name__=='__main__':main()
