#!/usr/bin/env python3
"""Exact finite checks for paper.tex. Python standard library only."""
from itertools import product, combinations_with_replacement
from collections import Counter
from fractions import Fraction


def points(p,r):
    return product(range(p), repeat=r)


def directions(p,r):
    for i in range(r):
        for tail in points(p,r-i-1):
            yield (0,)*i+(1,)+tail


def bound(p,r,k):
    z=1; a=0
    while z*p<=k: z*=p; a+=1
    b=k//z
    return Fraction(p-1,p**r) if a>=r-1 else Fraction((p-1)*(p+1-b),p**(a+2))


def signature(packet,p,vectors):
    ans=[]
    for v in vectors:
        counts=[0]*p
        for u in packet:
            counts[sum(x*y for x,y in zip(u,v))%p]+=1
        ans.append(tuple(counts))
    return tuple(ans)


def density(A,C,p,r):
    V=list(directions(p,r))
    return Fraction((p-1)*sum(a!=c for a,c in zip(signature(A,p,V),signature(C,p,V))),p**r)


def brute(p,r,k):
    V=list(directions(p,r)); X=list(points(p,r))
    sig=[signature(A,p,V) for A in combinations_with_replacement(X,k)]
    mn=len(V)+1; pairs=0
    for i,a in enumerate(sig):
        for c in sig[:i]:
            d=sum(x!=y for x,y in zip(a,c)); assert d>0
            mn=min(mn,d); pairs+=1
    actual=Fraction((p-1)*mn,p**r)
    assert actual==bound(p,r,k),(p,r,k,actual,bound(p,r,k))
    print(f'exhaustive ell={p}, rank={r}, k={k}: {len(sig)} packets, {pairs} pairs, min={actual}')
    return pairs


FACTORS={1:[(1,0)],2:[(1,0),(0,1)],3:[(1,0),(0,1),(1,1)],
         4:[(1,0),(0,1),(1,1),(1,-1)],6:[(1,0),(0,1),(1,1),(2,1),(3,1),(3,2)]}


def expand(factors):
    D={(0,0):1}
    for a,b in factors:
        E=Counter(D)
        for (i,j),c in D.items(): E[i+a,j+b]-=c
        D={k:v for k,v in E.items() if v}
    return D


def arrays(p,D):
    E=Counter()
    for (i,j),c in D.items(): E[i%p,j%p]+=c
    A=[]; C=[]
    for u,c in E.items():
        (A if c>0 else C).extend([u]*abs(c))
    return A,C


def lift(p,r,a,A,C):
    assert a+2<=r
    return ([u+z+(0,)*(r-a-2) for u in points(p,a) for z in A],
            [u+z+(0,)*(r-a-2) for u in points(p,a) for z in C])


def split_conic(p,b):
    B=[z for z in range(1,p) if pow(z,b,p)==1]
    assert len(B)==b
    lam=next(z for z in range(1,p) if z not in B)
    return ([(z,pow(z,-1,p)) for z in B],
            [(z,pow(z,-1,p)) for z in [(lam*x)%p for x in B]])


def nonsplit_conic(p,b):
    d=next(x for x in range(1,p) if pow(x,(p-1)//2,p)==p-1)
    def mul(z,w): return ((z[0]*w[0]+d*z[1]*w[1])%p,(z[0]*w[1]+z[1]*w[0])%p)
    def power(z,n):
        w=(1,0)
        for _ in range(n): w=mul(w,z)
        return w
    norm1=[(x,y) for x,y in points(p,2) if (x*x-d*y*y)%p==1]
    B=[z for z in norm1 if power(z,b)==(1,0)]
    assert len(B)==b
    lam=next(z for z in norm1 if z not in B)
    return B,[mul(lam,z) for z in B]


def check(p,b,A,C,kind):
    assert len(A)==len(C)==b and not(set(A)&set(C))
    actual=density(A,C,p,2)
    assert actual==bound(p,2,b),(p,b,kind,actual,bound(p,2,b))
    # Integer-scaled Fourier norm: each line contributes p at its annihilator,
    # and subtracting the common origin contributes -c everywhere.
    V=list(directions(p,2))
    S=[v for v,a,c in zip(V,signature(A,p,V),signature(C,p,V)) if a!=c]
    c=len(S); assert c==p+1-b
    norm=Fraction(sum(abs(p*sum(sum(x*y for x,y in zip(u,v))%p==0 for v in S)-c)
                      for u in points(p,2)),p*p)
    assert norm==2*b*actual,(p,b,norm,actual)
    return actual


def main():
    total=0
    for p,r,k in [(3,1,1),(3,2,1),(3,2,2),(3,2,3),(3,3,1),(3,3,2),(5,2,1),(5,2,2),(5,3,1)]:
        total+=brute(p,r,k)
    print(f'Total exhaustive pairs: {total}')
    for b,F in FACTORS.items():
        D=expand(F)
        assert len(D)==2*b and set(D.values())=={-1,1} and sum(D.values())==0
        print(f'Laurent identity b={b}: {sorted(D.items())}')
    n=0; lifts=0
    for p in (3,5,7,11,13,17,19,23,29,31):
        results={}
        for b,F in FACTORS.items():
            if b>=p: continue
            A,C=arrays(p,expand(F)); results[b]=check(p,b,A,C,'factor'); n+=1
            if p<=7:
                AA,CC=lift(p,3,1,A,C); assert density(AA,CC,p,3)==bound(p,3,b*p); lifts+=1
        A=[(j,0) for j in range(1,p)]; C=[(0,j) for j in range(1,p)]
        results[p-1]=check(p,p-1,A,C,'last'); n+=1
        for b in range(1,p):
            if b<p-1 and (p-1)%b==0:
                A,C=split_conic(p,b); results[b]=check(p,b,A,C,'split'); n+=1
            if (p+1)%b==0:
                A,C=nonsplit_conic(p,b); results[b]=check(p,b,A,C,'nonsplit'); n+=1
        print(f'ell={p}: verified sharp phases '+', '.join(f'{b}:{d}' for b,d in sorted(results.items())))
    # Saturation in rank 1 through 4, using a subspace and its disjoint translate.
    for p in (3,5,7):
        for r in range(1,5 if p==3 else 4):
            A=[u+(0,) for u in points(p,r-1)]; C=[u+(1,) for u in points(p,r-1)]
            assert density(A,C,p,r)==bound(p,r,len(A))==Fraction(p-1,p**r)
            lifts+=1
    print(f'Base construction and Fourier-norm tests: {n}; lift/saturation tests: {lifts}')
    print('All exact checks passed.')

if __name__=='__main__': main()
