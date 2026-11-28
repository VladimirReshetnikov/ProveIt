#!/usr/bin/env python3
"""Exact finite regressions for the dyadic-shift coloring (not a formal proof)."""
from collections import defaultdict
from math import gcd, isqrt
from itertools import combinations_with_replacement


def colors(s, B, h):
    M, H = 1 << s, 1 << h
    k = (s+h-1)//h
    for e in range(M):
        c, energy = [], 0
        for j in range(k):
            r = (e << (j*h)) % M
            cell, t = divmod(B*r, M)
            c.append(cell)
            energy += t*t
        yield tuple(c)+(2*H*H*energy//(B*M*M),)


def classes(s, B, h):
    D = defaultdict(list)
    for e, c in enumerate(colors(s, B, h)):
        D[c].append(e)
    return D


def check_separation(s,h):
    M,H,k=1<<s,1<<h,(s+h-1)//h
    for d in range(1,M):
        v=(d & -d).bit_length()-1
        j=(s-1-v)//h
        assert 0<=j<k
        r=(d<<(j*h))%M
        assert r and H*min(r,M-r)>=M


def check_weighted(s,B,h):
    M,H,k=1<<s,1<<h,(s+h-1)//h
    D=classes(s,B,h)
    assert len(D)<=B**k*(1+2*k*H*H//B)
    tested=0
    # Check unordered endpoint pairs (swapping coefficients covers both orders),
    # all positive coefficients of total <= B,
    # and every possible midpoint solving the modular equation (including nonunits).
    for A in D.values():
        S=set(A)
        for u,w in combinations_with_replacement(A,2):
            for a in range(1,B):
                for b in range(1,B-a+1):
                    n=a+b; g=gcd(n,M); rhs=(a*u+b*w)%M
                    if rhs%g: continue
                    mod=M//g
                    root=0 if mod==1 else (rhs//g)*pow(n//g,-1,mod)%mod
                    for j in range(g):
                        v=root+j*mod
                        assert v not in S or u==v==w, (s,B,h,u,v,w,a,b)
                        tested+=1
    return len(D),max(map(len,D.values())),tested


def prime_list(L):
    return [p for p in range(2,L+1) if all(p%d for d in range(2,isqrt(p)+1))]


def sparse_transfer(s,z,L,q0=18480):
    M=1<<s; q=q0*3*z*M; B=2*z
    assert 2*z*(L+1)<M and z>=1
    h=max(1,(s+1)//2)
    D=classes(s,B,h)
    A=max(D.values(),key=len)
    g=1+3*z*q0
    T={-pow(g,e,q)%q for e in A}
    assert len(T)==len(A) and all(t%q0==q0-1 for t in T)
    checks=0
    for p in prime_list(L):
        m=q
        while m%p==0: m//=p
        U={t%m for t in T}
        for a in U:
            hits=0; v=a
            for i in range(1,z):
                v=v*p%m
                if v in U or -v%m in U: hits+=1
                assert hits<=1, (s,z,L,p,a,i)
                checks+=1
    return len(T),checks


def check_bound():
    count=0
    for B in (162,486,1458,4374):
        for n in range(1,7):
            for W in (B**n, B**n+1, 2*B**n-1):
                H=1<<(W-1).bit_length()
                for s in (1, H.bit_length()-1, n*(H.bit_length()-1)):
                    if (1<<s)>W**n: continue
                    h=H.bit_length()-1; k=(s+h-1)//h
                    assert k<=n and W<=H<2*W
                    C=B**k*(1+2*k*H*H//B)
                    assert 3*(B//2)*C<=W**4
                    count+=1
    return count


def l0(s):
    a=1
    while a*3<=s: a*=3
    return a*81


def optimized_bits(s):
    z=l0(s); B=2*z; q=(B-1).bit_length()
    h=isqrt(s*q)
    if h*h<s*q: h+=1
    k=(s+h-1)//h
    # A rigorous integer upper bound for log_2(3*z*C):
    return h,k,(9*z*k-1).bit_length()+q*k+2*h


if __name__=='__main__':
    cases=0
    for s in range(1,13):
        for h in range(1,s+3):
            check_separation(s,h); cases+=1
    print(f'Separation: {cases} (s,h) cases; every nonzero difference checked.')
    total=0; nonsingle=0
    for s in range(1,11):
        for B in (2,3,4,5,8):
            for h in (1, max(1,s//2), s, s+1):
                c,m,t=check_weighted(s,B,h)
                total+=t; nonsingle+=m>1
    print(f'Weighted congruences: {total:,} midpoint checks; {nonsingle} cases with nonsingleton colors.')
    for s,z,L in [(12,3,19),(14,9,19),(14,l0(14),5)]:
        n,c=sparse_transfer(s,z,L)
        print(f'Sparse transfer: s={s}, z={z}, L={L}, selected={n}, {c} exponent tests.')
    print(f'W^4 bound: {check_bound()} integer parameter cases.')
    print('Optimized log2 loss upper bounds (not enumeration):')
    for s in (44,1000,10000,1000000,100000000):
        h,k,b=optimized_bits(s)
        print(f'  s={s:>9}, h={h:>6}, k={k:>5}, bits <= {b:>8}, bits/s <= {b/s:.6f}')
    print('PASS: all exact finite assertions.')
