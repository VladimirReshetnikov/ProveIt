#!/usr/bin/env python3
"""Exact finite-field checks for the Euler-packet paper. No dependencies.
All histogram comparisons use integers; prime count example is illustrative.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from fractions import Fraction
from math import isqrt


def vectors(p,r): return list(product(range(p), repeat=r))
def directions(p,r):
    return [(0,)*j+(1,)+z for j in range(r) for z in product(range(p),repeat=r-j-1)]
def dot(a,v,p): return sum(x*y for x,y in zip(a,v))%p

def signature(A,p,r):
    out=[]
    for v in directions(p,r):
        hist=[0]*p
        for a in A: hist[dot(a,v,p)]+=1
        out.append(tuple(hist))
    return tuple(out)

def distance(A,B,p,r):
    return Fraction((p-1)*sum(a!=b for a,b in zip(signature(A,p,r),signature(B,p,r))),p**r)

def universal(p,r,k): return Fraction(p-1,p*min(k,p**(r-1)))
def small(p,r,k): return Fraction(p-1,p*p)*(p+1-k) if r>=2 and k<=p else Fraction(0)

def exhaustive(p,r,k,expected):
    ps=vectors(p,r); ds=directions(p,r)
    packets=list(combinations_with_replacement(ps,k))
    # Intern each direction's histogram; pack all directions in fixed-width fields.
    # A bit at the top of each field indicates a differing histogram after XOR.
    tables=[{} for _ in ds]; raw=[]
    for A in packets:
        row=[]
        for t,v in zip(tables,ds):
            counts=[0]*p
            for a in A: counts[dot(a,v,p)]+=1
            h=tuple(counts)
            row.append(t.setdefault(h,len(t)))
        raw.append(row)
    nbits=max(1,max(len(t) for t in tables).bit_length()); stride=nbits+1
    ms=sum(1<<(i*stride+nbits) for i in range(len(ds)))
    ids=[sum(a<<(i*stride) for i,a in enumerate(row)) for row in raw]
    # All fields have a sentinel bit. Subtract one from each field independently;
    # zero fields lose sentinel, nonzero fields retain it.
    ones=sum(1<<(i*stride) for i in range(len(ds)))
    best=len(ds)+1; witnesses=0; total=0
    for i,a in enumerate(ids):
        for b in ids[:i]:
            d=((((a^b)|ms)-ones)&ms).bit_count()
            assert d>0
            if d<best: best=d; witnesses=1
            elif d==best: witnesses+=1
            total+=1
    val=Fraction((p-1)*best,p**r)
    assert val>=max(universal(p,r,k),small(p,r,k))
    assert val==expected,(p,r,k,val,expected)
    print(f'exhaustive p={p}, r={r}, k={k}: packets={len(packets)}, pairs={total}, min={val}, minimizers={witnesses}')


def field_ops(p):
    D=next(d for d in range(1,p) if pow(d,(p-1)//2,p)==p-1)
    one=(1,0)
    def mul(x,y): return ((x[0]*y[0]+D*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
    def power(x,n):
        z=one
        while n:
            if n&1:z=mul(z,x)
            x=mul(x,x);n//=2
        return z
    def conj(x):return (x[0],-x[1]%p)
    return mul,power,conj


def split(p,k):
    z=next(z for z in range(1,p) if pow(z,k,p)==1 and len({pow(z,i,p) for i in range(k)})==k)
    A=[(pow(z,i,p),0) for i in range(k)]
    B=[(0,pow(z,i,p)) for i in range(k)]
    return A,B


def nonsplit(p,k):
    mul,power,conj=field_ops(p)
    z=next(z for z in vectors(p,2) if z!=(0,0) and power(z,k)==(1,0) and len({power(z,i) for i in range(k)})==k)
    U={power(z,i) for i in range(k)}
    for a in vectors(p,2):
        if a==(0,0):continue
        A={mul(u,a) for u in U}; B={mul(u,conj(a)) for u in U}
        if A.isdisjoint(B):return sorted(A),sorted(B)
    raise AssertionError('no disjoint orbit')


def slope(a,b,p):
    x=(b[0]-a[0])%p;y=(b[1]-a[1])%p
    if not x:return p
    return y*pow(x,-1,p)%p


def plane_7_5():
    # Equality requires 5 cross-directions; the other 3 can be sent to
    # infinity, zero, one by an invertible linear map. Translate one A point to 0.
    p=7; D=tuple(range(2,7)); P=vectors(p,2); best=0; distribution=Counter(); count=0
    for xs in product(range(1,p),repeat=5):
        B=tuple((x,x*s%p) for x,s in zip(xs,D)); count+=1
        eligible=[a for a in P if a not in B and tuple(sorted(slope(a,b,p) for b in B))==D]
        assert (0,0) in eligible
        best=max(best,len(eligible)); distribution[len(eligible)]+=1
    assert count==6**5 and best==4
    A,B=nonsplit(7,4)
    A=A+[(0,0)];B=B+[(0,0)]
    assert distance(A,B,7,2)==Fraction(24,49)
    print(f'plane p=7,k=5: {count} normalized candidates, maximum eligible A size={best}, histogram={dict(sorted(distribution.items()))}; exact min=24/49')


def constructions():
    count=0
    for p in (3,5,7,11,13,17,19,23,29,31,37,41,43):
        for k in range(2,p):
            if (p-1)%k==0:
                A,B=split(p,k)
                assert len(set(A))==len(set(B))==k and set(A).isdisjoint(B)
                assert distance(A,B,p,2)==small(p,2,k);count+=1
            if (p+1)%k==0:
                A,B=nonsplit(p,k)
                assert len(set(A))==len(set(B))==k and set(A).isdisjoint(B)
                assert distance(A,B,p,2)==small(p,2,k);count+=1
    print(f'dihedral constructions: {count} checked (split and nonsplit)')
    count=0
    for p,r in ((3,1),(3,2),(3,3),(3,4),(5,2),(5,3),(7,2),(7,3)):
        for s in range(r):
            A=[v+(0,)*(r-s) for v in vectors(p,s)]
            B=[v[:s]+(1,)+v[s+1:] for v in A]
            k=p**s; assert distance(A,B,p,r)==universal(p,r,k);count+=1
    print(f'power-size coset constructions: {count} checked')


def arithmetic_example(limit=1000000):
    # independent cubic characters modulo 13 and 19; primitive root tables.
    def exp_table(q):
        g=next(g for g in range(2,q) if len({pow(g,i,q) for i in range(q-1)})==q-1)
        return {pow(g,i,q):i%3 for i in range(q-1)}
    T,U=exp_table(13),exp_table(19)
    sieve=bytearray(b'\x01')*(limit+1);sieve[:2]=b'\x00\x00'
    for p in range(2,isqrt(limit)+1):
        if sieve[p]:sieve[p*p::p]=b'\x00'*((limit-p*p)//p+1)
    pairs=[([(1,0),(2,0)],[(0,1),(0,2)]), ([(0,0),(1,0),(2,0)],[(0,1),(1,1),(2,1)])]
    total=0;bad=[0,0]
    for p in range(limit//2+1,limit+1):
        if not sieve[p] or p%13==0 or p%19==0:continue
        total+=1;v=(T[p%13],U[p%19])
        for i,(A,B) in enumerate(pairs):
            bad[i]+=sorted(dot(a,v,3) for a in A)!=sorted(dot(b,v,3) for b in B)
    print(f'illustration Q=247, primes in ({limit//2},{limit}]: {total}; k=2 disagreements={bad[0]} ({bad[0]/total:.6f}, limit 4/9); k=3 disagreements={bad[1]} ({bad[1]/total:.6f}, limit 2/9)')


if __name__=='__main__':
    for p,r,k,d in [(3,1,3,Fraction(2,3)),(3,2,1,Fraction(2,3)),(3,2,2,Fraction(4,9)),(3,2,3,Fraction(2,9)),(3,2,4,Fraction(2,9)),(3,3,2,Fraction(4,9)),(5,2,2,Fraction(16,25)),(5,2,3,Fraction(12,25))]:
        exhaustive(p,r,k,d)
    constructions();plane_7_5();arithmetic_example()
    print('ALL CHECKS PASSED')
