#!/usr/bin/env python3
"""Exact finite-field analogues of the descent averaging argument.
These do not test the adelic theta lift or prove the analytic result.
No third-party dependencies. Run: python3 check_average.py
"""
from itertools import product
from fractions import Fraction as F
from random import Random


def matrices(p, n, r):
    return product(range(p), repeat=n*r)


def mm(a, b, n, k, r, p):
    return tuple(sum(a[i*k+j]*b[j*r+t] for j in range(k)) % p
                 for i in range(n) for t in range(r))


def det2(a, p):
    return (a[0]*a[3]-a[1]*a[2]) % p


def sign_perm(xs):
    return (-1)**sum(xs[i]>xs[j] for i in range(len(xs)) for j in range(i+1,len(xs)))


def sign_gl2_f2(a):
    v = [(0,1),(1,0),(1,1)]
    return sign_perm([v.index(mm(a,x,2,2,1,2)) for x in v])


def quadratic(a,p):
    assert a % p
    return 1 if pow(a,(p-1)//2,p)==1 else -1


def verify(p,r,chosen,nontrivial=True):
    # n=r+1. For r=1 use quadratic determinant; for r=2,p=2 use sign of GL2(F2).
    n=r+1
    assert r==1 or (r==2 and p==2 and chosen)
    def top(h): return tuple(h[i*n+j] for i in range(r) for j in range(r))
    def td(a): return a[0] if r==1 else det2(a,p)
    def rho(h):
        if not nontrivial: return 1
        return quadratic(top(h)[0],p) if r==1 else sign_gl2_f2(top(h))
    H=[]
    for h in matrices(p,n,n):
        if td(top(h))==0 or h[-1]==0: continue
        if chosen and any(h[r*n+j] for j in range(r)): continue
        if not chosen and any(h[i*n+r] for i in range(r)): continue
        H.append(h)
    X=list(matrices(p,n,r)); I=tuple(int(i==j) for i in range(n) for j in range(n))
    inv={h:next(k for k in H if mm(h,k,n,n,n,p)==I) for h in H}
    assert all(rho(mm(h,k,n,n,n,p))==rho(h)*rho(k) for h in H for k in H)
    K=[h for h in H if not chosen or top(h)==tuple(int(i==j) for i in range(r) for j in range(r))]
    def good(x): return td(x[:r*r])!=0 and (not chosen or all(z==0 for z in x[r*r:]))
    def avg(psi):
        return {x:F(sum(psi[mm(inv[h],x,n,n,r,p)]*rho(h) for h in H),len(H)) for x in X}
    # Every delta basis function, not just random examples: projection kills bad support.
    for z in X:
        f=avg({x:int(x==z) for x in X})
        if nontrivial: assert all(f[x]==0 for x in X if not good(x))
        assert all(f[mm(h,x,n,n,r,p)]==rho(h)*f[x] for h in H for x in X)
    # Good K-orbits match translated block data (on finite fields).
    remaining={x for x in X if good(x)}; orbits=[]
    while remaining:
        z=min(remaining); orb={mm(k,z,n,n,r,p) for k in K}; assert orb<=remaining
        remaining-=orb; orbits.append(orb)
        if chosen: assert len(orb)==1
        else: assert len(orb)==(p-1)*p # rank one, any nonzero top and any bottom
    # Explicit hyperplane shear witness for every bad x, with negative character.
    if nontrivial:
        for x in X:
            if good(x): continue
            witnesses=[h for h in H if rho(h)==-1 and mm(h,x,n,n,r,p)==x]
            assert witnesses, (p,r,chosen,x)
    else:
        f=avg({x:int(not good(x)) for x in X})
        assert any(f[x]!=0 for x in X if not good(x))
    print(f'p={p}, rank={r}, chosen={chosen}, nontrivial={nontrivial}: '
          f'|H|={len(H)}, |X|={len(X)}, good orbits={len(orbits)}; all tests passed')

if __name__=='__main__':
    verify(3,1,True)
    verify(3,1,False)
    verify(2,2,True)
    verify(3,1,True,False)  # counterexample if chosen annihilation is dropped
    verify(3,1,False,False) # counterexample if twist character is trivial
