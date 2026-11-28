#!/usr/bin/env python3
"""Exact checks for the finite-word and torsion-node covering theorems.
No numerical p-adic approximations or external packages are used.
"""
from itertools import product, combinations
from fractions import Fraction
from math import ceil


def edges(E):
    L=max(E)
    if L==0:
        return {(): [((),1)]}
    return {u:[(u[1:]+(d,),d) for d in (0,1)
               if any((u+(d,))[a] for a in E)]
            for u in product((0,1),repeat=L)}


def min_word(E,M):
    """Minimum weight of M bits hitting each translate t+E contained in the word."""
    E=tuple(sorted(set(E)))
    L=max(E)
    if M<=L:
        return 0
    G=edges(E)
    if L==0:
        return M
    dp={u:sum(u) for u in G}
    for _ in range(M-L):
        nxt={}
        for u,c in dp.items():
            for v,d in G[u]:
                nxt[v]=min(nxt.get(v,M+1),c+d)
        dp=nxt
    return min(dp.values())


def brute_word(E,M):
    return min(sum(b) for b in product((0,1),repeat=M)
               if all(any(b[t+a] for a in E) for t in range(M-max(E))))


def min_cycle(E):
    """Karp minimum cycle mean, with a zero-cost super-source to every state.
    Dynamic program for min weight of length k paths ending at v.
    """
    G=edges(E); states=list(G); n=len(states)
    dp=[{u:0 for u in states}]
    for k in range(1,n+1):
        nxt={}
        for u,c in dp[-1].items():
            for v,d in G[u]:
                nxt[v]=min(nxt.get(v,n+1),c+d)
        dp.append(nxt)
    return min(max(Fraction(dp[n][v]-dp[k][v],n-k)
                       for k in range(n) if v in dp[k]) for v in dp[n])


def min_set_cover(V, hyperedges, w):
    """Exhaustive exact hitting set; only used on small cases."""
    V=tuple(V); best=None
    for b in product((0,1),repeat=len(V)):
        D={v for v,k in zip(V,b) if k}
        if all(D & e for e in hyperedges):
            c=sum((w[v] for v in D),Fraction(0))
            if best is None or c<best:
                best=c
    return best


def vp_int(n,p):
    k=0
    while n and n%p==0: n//=p; k+=1
    return k


def level(n,p,H):
    return 0 if not n else H-vp_int(n,p)


def r_h(p,h):
    return Fraction(1,(p-1)*p**(h-1))


def node_cover(p,S,J,r):
    H=max(S); mod=p**H
    A=[a for a in range(1,mod) if level(a,p,H) in S]
    es=[{j*a%mod for j in J} for a in A]
    V=sorted(set.union(*es))
    w={a:r if a==0 else min(r,r_h(p,level(a,p,H))) for a in V}
    return min_set_cover(V,es,w)


def level_cover(p,S,E,r):
    es=[{max(h-a,0) for a in E} for h in S]
    V=sorted(set.union(*es))
    w={h:r if h==0 else min(Fraction(1),r/r_h(p,h)) for h in V}
    return min_set_cover(V,es,w)


def main():
    checked=0
    for L in range(1,5):
        for bits in product((0,1),repeat=L-1):
            E=(0,)+tuple(i+1 for i,b in enumerate(bits) if b)+(L,)
            delta=min_cycle(E)
            assert delta>=Fraction(1,len(E))
            for M in range(L+1,12):
                D=min_word(E,M)
                assert D==brute_word(E,M),(E,M,D)
                assert delta*(M-L-(2**L-1))<=D<=delta*M,(E,M,D,delta)
                checked+=1
    print(f'finite-word DP vs exhaustive search: {checked} instances passed')
    # exact dual potential for E=(0,1,3)
    E=(0,1,3); G=edges(E)
    pot=dict(zip(G,(-6,-3,-2,0,-4,0,-2,0)))
    slacks=[5*d-2-(pot[v]-pot[u]) for u in G for v,d in G[u]]
    b=(0,0,0,1,1)
    assert min(slacks)>=0
    assert all(any(b[(t+a)%5] for a in E) for t in range(5))
    assert min_cycle(E)==Fraction(2,5)
    print('E={0,1,3}: all',len(slacks),'dual inequalities verified; periodic 00011 gives mean 2/5')
    costs=word_costs(E,1003)
    for N in range(1,1001):
        assert costs[N+3]==(2*N+4)//5
    print('E={0,1,3}: exact formula ceil(2N/5) verified for N=1,...,1000')
    print('N | exact C1 | chain lower bound (all dimensions) | explicit upper')
    for N in [1,2,3,4,5,6,10,20,50,100,200,1000]:
        D=min_word(E,N+3)
        # Only M up to N+L; DP evaluated incrementally below for efficiency.
        ds=word_costs(E,N+3)
        lower=max(Fraction(N,len(E)),
                  max(Fraction(ds[M]*(N-M+4),M) for M in range(4,N+4)))
        assert lower<=D
        print(f'{N:4d} | {D:4d} | {str(lower):>11s} ({float(lower):8.3f}) | {D:4d}')
    checked=0
    for p,H in [(2,3),(3,2)]:
        for lo in range(1,H+1):
            for hi in range(lo,H+1):
                S=set(range(lo,hi+1))
                for E in [(0,1),(0,2),(0,1,2)]:
                    for r in [r_h(p,lo),p*r_h(p,lo),Fraction(3)]:
                        a=node_cover(p,S,[p**j for j in E],r)
                        c=level_cover(p,S,E,r)
                        assert a==c,(p,S,E,r,a,c)
                        checked+=1
    print(f'node-level hitting set equivalence: {checked} exhaustive instances passed')
    checked=0
    for p,H in [(2,3),(3,2)]:
        for lo in range(1,H+1):
            S=set(range(lo,H+1))
            for j,k in combinations(range(1,8),2):
                r=p*r_h(p,lo)
                a=node_cover(p,S,[j,k],r)
                c=pair_cover(p,S,j,k,r)
                assert a==c,(p,S,j,k,r,a,c)
                checked+=1
    print(f'arbitrary two-power formula: {checked} exhaustive instances passed')
    for N in range(1,80):
        assert min_word((0,1),N+1)==ceil(N/2)
    print('two-power one-variable formula: N=1,...,79 verified')


def pair_cover(p,S,j,k,r):
    b=vp_int(j,p); c=vp_int(k,p)
    if b>c: return pair_cover(p,S,k,j,r)
    T={max(h-b,0) for h in S}
    w=lambda h: r if h==0 else min(Fraction(1),r/r_h(p,h))
    if b<c:
        es=[{t,max(t-(c-b),0)} for t in T]
        V=sorted(set.union(*es));return min_set_cover(V,es,{h:w(h) for h in V})
    out=r if 0 in T else Fraction(0)
    for t in T-{0}:
        m=p**t;u=(k//p**b)*pow(j//p**b,-1,m)%m
        d=1;z=u
        while z!=1: z=z*u%m;d+=1
        out+=w(t)*Fraction((d+1)//2,d)
    return out

def word_costs(E,M):
    L=max(E); G=edges(E); dp={u:sum(u) for u in G}; out={L:min(dp.values())}
    for k in range(L+1,M+1):
        nxt={}
        for u,c in dp.items():
            for v,d in G[u]:
                nxt[v]=min(nxt.get(v,k+1),c+d)
        dp=nxt;out[k]=min(dp.values())
    return out

if __name__=='__main__':main()
