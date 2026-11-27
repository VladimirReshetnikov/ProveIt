#!/usr/bin/env python3
"""Exact finite-shell minimax costs for cyclotomic packets.

Python standard library only. Shells and the number of colors must be small:
this is a finite exhaustive algorithm, not an efficient large-H implementation.
All calculations are integers or fractions, and strict blocking is respected.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations_with_replacement, product
import argparse
import json


def phi(p,h):
    return (p-1)*p**(h-1)


def vp_nonzero(a,p):
    k=0
    while a%p==0:
        k+=1; a//=p
    return k


@lru_cache(None)
def shell_layouts(p,h):
    """(root count, potential vector), in units of r_h; None means infinity."""
    e=phi(p,h)
    units=[a for a in range(1,p**h) if a%p]
    D=[[None if a==b else p**vp_nonzero(a-b,p)-1 for b in units] for a in units]
    out=[]
    for m in range(e):
        profiles=set()
        for roots in combinations_with_replacement(range(e),m):
            t=tuple(None if j in roots else sum(D[j][b] for b in roots) for j in range(e))
            profiles.add(t)
        out.extend((m,t) for t in profiles)
    # At m=e, the full shell dominates every other layout of equal count.
    out.append((e,(None,)*e))
    return tuple(out)


@lru_cache(None)
def options(p,h,slack,T):
    """All different (count, clipped positive-loss vector) for a color."""
    return tuple(sorted({(m,tuple(T if v is None else min(T,max(0,v-slack)) for v in t))
                        for m,t in shell_layouts(p,h)}))


def exact_cost(p,h0,H,n,delta=Q(0),details=False):
    """Minimum total cost for AT MOST n members; constants pad unused colors.

    State after shell h: sorted (root count, total valuation budget in units r_h)
    for each polynomial.  The full state suffices because the earlier-shell
    loss offset at the next shell is p*scaled_budget - root_count.
    """
    if not (n>=1 and 1<=h0<=H and delta>=0):
        raise ValueError('require n>=1, 1<=h0<=H, delta>=0')
    states={((0,0),)*n}
    sizes=[]
    for h in range(h0,H+1):
        e=phi(p,h)
        T=int(delta*e)+1  # min integer strictly above delta*e
        new=set()
        for state in states:
            pools=[options(p,h,p*K-M,T) for M,K in state]
            for choices in product(*pools):
                if not all(sum(choice[1][j] for choice in choices)>=T for j in range(e)):
                    continue
                nxt=tuple(sorted((M+m,p*K+m) for (M,K),(m,_) in zip(state,choices)))
                new.add(nxt)
        states=new
        sizes.append(len(states))
    best=min(Q(sum(K for _,K in s),phi(p,H)) for s in states)
    return (best,sizes) if details else best


def capacity(p,h,m):
    e=phi(p,h)
    if m==e: return None
    return Q(sum(phi(p,j)*(m//phi(p,j)) for j in range(1,h)),e)


def block_partition_cost(p,h0,H,n):
    """Minimum among consecutive single-member blocks at tolerance zero."""
    @lru_cache(None)
    def f(a,k):
        if a>H:return Q(0)
        if k==1:return Q(H-a+1,p**(a-1))
        return min(Q(b-a+1,p**(a-1))+f(b+1,k-1) for b in range(a,H+1))
    return f(h0,n)


def unrestricted_cost(p,h0,H,delta):
    return sum((Q(next(m for m in range(phi(p,h)+1)
                     if capacity(p,h,m) is None or capacity(p,h,m)>delta),phi(p,h))
                for h in range(h0,H+1)),Q(0))


def verify():
    # Exact check of one-shell maximin, including multiplicities.
    cap_checks=0
    for p,h in [(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(5,1)]:
        e=phi(p,h)
        maxima={m:-1 for m in range(e)}
        for m,t in shell_layouts(p,h):
            if m<e:
                maxima[m]=max(maxima[m],min(x for x in t if x is not None))
        for m in range(e):
            assert Q(maxima[m],e)==capacity(p,h,m)
            cap_checks+=1
    print('One-shell capacity checks:',cap_checks)
    print('p h0 H n delta cost partition_upper unrestricted_lower states')
    for p,h0,H,n,delta in [(2,1,H,n,Q(0)) for H in range(1,4) for n in range(1,4)] + [
        (3,1,2,n,Q(0)) for n in (1,2)] + [(2,2,3,n,Q(0)) for n in (1,2)] + [
        (2,1,3,n,Q(1,4)) for n in (1,2,3)]:
        best,sizes=exact_cost(p,h0,H,n,delta,True)
        lo=unrestricted_cost(p,h0,H,delta)
        assert best>=lo
        up=block_partition_cost(p,h0,H,n) if delta==0 else None
        if up is not None:assert best<=up
        if n==1 and delta==0:assert best==Q(H-h0+1,p**(h0-1))
        if n>=H-h0+1:assert best==lo
        print(p,h0,H,n,str(delta),str(best),str(up),str(lo),','.join(map(str,sizes)))
    print('All exact checks passed. These are sanity checks, not a proof of the asymptotic law.')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify',action='store_true')
    parser.add_argument('--p',type=int,default=2)
    parser.add_argument('--h0',type=int,default=1)
    parser.add_argument('--H',type=int,default=3)
    parser.add_argument('--n',type=int,default=2)
    parser.add_argument('--delta',type=Q,default=Q(0))
    args=parser.parse_args()
    if args.verify:verify()
    else:
        cost,sizes=exact_cost(args.p,args.h0,args.H,args.n,args.delta,True)
        print(json.dumps({'cost':str(cost),'states_per_shell':sizes},indent=2))
