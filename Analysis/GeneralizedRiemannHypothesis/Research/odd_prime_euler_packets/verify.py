#!/usr/bin/env python3
"""Exact finite-field checks. Only Python's standard library; no numerical roots.
Disjoint residual multisets suffice because common factors can be padded.
Tests are not formal proofs.
"""
from itertools import product, combinations_with_replacement
from collections import Counter

def points(p,r): return list(product(range(p),repeat=r))
def directions(p,r): return [v for v in points(p,r) if any(v) and next(x for x in v if x)==1]
def setup(p,r):
    P,V=points(p,r),directions(p,r)
    ev=[tuple(sum(x*y for x,y in zip(a,v))%p for v in V) for a in P]
    return P,V,ev

def signature(indices,ev,p,J):
    h=[[0]*p for _ in range(J)]
    for a in indices:
        for j,t in enumerate(ev[a]): h[j][t]+=1
    return tuple(tuple(x) for x in h)

def cosets(A,B,p):
    if len(set(A))!=len(A) or len(set(B))!=len(B): return False
    def shift(S): return {tuple((x-y)%p for x,y in zip(b,S[0])) for b in S}
    U=shift(A)
    return U==shift(B) and all(tuple((x+y)%p for x,y in zip(a,b)) in U for a in U for b in U)

def exhaustive(p,r,max_k):
    P,V,ev=setup(p,r); total=0; best=len(V)+1
    for k in range(1,max_k+1):
        M=list(combinations_with_replacement(range(len(P)),k))
        rec=[(a,set(a),signature(a,ev,p,len(V)),sum(m*m for m in Counter(a).values())) for a in M]
        counts=Counter()
        for i,(a,sa,ha,e2a) in enumerate(rec):
            for b,sb,hb,e2b in rec[i+1:]:
                if not sa.isdisjoint(sb): continue
                d=[sum((u-v)**2 for u,v in zip(x,y)) for x,y in zip(ha,hb)]
                J=sum(e>0 for e in d)
                assert J>0 and sum(d)==p**(r-1)*(e2a+e2b) and max(d)<=2*k*k
                assert J*k>=p**(r-1)
                if r>=2 and k<=p: assert J>=p**(r-2)*(p+1-k)
                if J*k==p**(r-1): assert cosets([P[t] for t in a],[P[t] for t in b],p)
                if r>=2:
                    assert J!=1 or k>=p**(r-1)
                    assert J!=2 or k>=(p-1)*p**(r-2)
                counts[J]+=1
        if counts: best=min(best,min(counts))
        total+=sum(counts.values())
        print(f'ell={p}, r={r}, k={k}: {sum(counts.values())} disjoint pairs; J spectrum={sorted(counts)}; padded min J={best}')
    return total

def count_J(A,B,p):
    P,V,ev=setup(p,len(A[0])); ind={a:i for i,a in enumerate(P)}
    ha=signature([ind[a] for a in A],ev,p,len(V)); hb=signature([ind[b] for b in B],ev,p,len(V))
    return sum(a!=b for a,b in zip(ha,hb))

def constructions():
    n=0
    for p in [2,3,5,7,11,13,17,19]:
        for r in range(1,4):
            if p**r>400: continue
            P=points(p,r)
            for d in range(r):
                A=[a for a in P if all(x==0 for x in a[d:])]
                B=[tuple((x+int(i==d))%p for i,x in enumerate(a)) for a in A]
                assert count_J(A,B,p)==p**(r-d-1); n+=1
            if r>=2:
                A=[a for a in P if a[0]==0 and a[1]!=0]; B=[a for a in P if a[1]==0 and a[0]!=0]
                assert len(A)==(p-1)*p**(r-2) and count_J(A,B,p)==2; n+=1
        for k in range(1,p):
            if (p-1)%k==0:
                M=[x for x in range(1,p) if pow(x,k,p)==1]
                assert len(M)==k and count_J([(m,0) for m in M],[(0,m) for m in M],p)==p+1-k; n+=1
        if p==2: continue
        nr=next(x for x in range(1,p) if pow(x,(p-1)//2,p)==p-1)
        def mul(a,b): return ((a[0]*b[0]+nr*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
        def fpow(a,k):
            b=(1,0)
            while k:
                if k&1: b=mul(b,a)
                a=mul(a,a); k//=2
            return b
        nonzero=[a for a in points(p,2) if any(a)]
        for k in range(1,p+1):
            if (p+1)%k: continue
            M=[a for a in nonzero if fpow(a,k)==(1,0)]; assert len(M)==k
            z=next(a for a in nonzero if fpow(a,p-1) not in M)
            A=[mul(m,z) for m in M]; B=[mul(m,fpow(z,p)) for m in M]
            assert set(A).isdisjoint(B) and count_J(A,B,p)==p+1-k; n+=1
    print(f'All {n} explicit construction tests passed.')

if __name__=='__main__':
    total=sum(exhaustive(p,r,k) for p,r,k in [(2,3,4),(3,2,4),(5,2,2),(3,3,2)])
    print(f'All {total} exhaustive disjoint-pair tests passed.')
    constructions()
