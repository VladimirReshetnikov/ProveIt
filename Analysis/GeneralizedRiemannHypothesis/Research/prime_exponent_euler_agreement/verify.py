#!/usr/bin/env python3
"""Exact finite-field checks of planar switching components; standard library only."""
from itertools import combinations, permutations, product
from math import gcd

def direction(p, u, v):
    x, y = (u[0]-v[0])%p, (u[1]-v[1])%p
    assert x or y
    return (y*pow(x,-1,p))%p if x else p

def good_directions(p,A,B):
    """Return directions of kernels for which projected multisets agree."""
    return tuple(t for t in range(p+1) if sorted((y-t*x)%p if t<p else x for x,y in A)==sorted((y-t*x)%p if t<p else x for x,y in B))

def find_full(p,b):
    """Exhaustive up to affine normalization when two good directions exist.
    Translate/scale axes separately to reduce each b-subset to orbit representative.
    A and B project injectively along every matching direction if there are b of them.
    """
    assert 2<=b<p
    reps=[]; seen=set()
    for S in combinations(range(p),b):
        if S not in seen:
            reps.append(S)
            seen.update(tuple(sorted((a*x+c)%p for x in S)) for a in range(1,p) for c in range(p))
    tested=0; perms=list(permutations(range(b)))
    for X,Y in product(reps,repeat=2):
        for ap in perms:
            A=tuple(zip(X,(Y[i] for i in ap)))
            for bp in perms:
                if any(i==j for i,j in zip(ap,bp)): continue
                B=tuple(zip(X,(Y[i] for i in bp)))
                tested+=1
                # all cross differences must have one of b directions; no duplicates in a row
                ds=set(direction(p,A[0],v) for v in B)
                if len(ds)!=b: continue
                if all(set(direction(p,u,v) for v in B)==ds for u in A[1:]) and all(len({direction(p,u,v) for u in A})==b for v in B):
                    assert len(good_directions(p,A,B))==b
                    return A,B,tested,len(reps)
    return None,None,tested,len(reps)

if __name__=='__main__':
    for p,b in [(3,2),(5,2),(5,3),(5,4),(7,2),(7,3),(7,4),(7,5),(7,6),(11,5)]:
        A,B,n,reps=find_full(p,b)
        assert bool(A) == ((p-1)%b == 0 or (p+1)%b == 0)
        print(f'p={p:2}, b={b}: {"YES" if A else "NO"}; normalized cases examined={n}, subset orbit reps={reps}')
        if A: print('   A=',A,' B=',B,' directions=',good_directions(p,A,B))
