#!/usr/bin/env python3
"""Exact integer tests for the quarter-density support theorem.
No external packages. The exhaustive oracle adds each labelled item to a box
or the reserve; it does not use the claimed inequalities or witness lists.
"""
from itertools import product
from functools import lru_cache
from random import Random


def cyclic4(supply, demand):
    u,v,w = supply; i,j,k = demand
    if not (u+w >= i+k and 3*u+2*v+w >= 3*i+2*j+k
            and u+2*v+3*w >= i+2*j+3*k
            and u+2*v+w >= i+2*j+k):
        return False
    if j>v and i<=u and k<=w:
        return (u-i)//2 + (w-k)//2 >= j-v
    return True


def klein4(supply, demand):
    u,v,w = supply; i,j,k = demand
    return u+v>=i+j and u+w>=i+k and v+w>=j+k


def full_cyclic4(supply, r):
    u,v,w = supply
    return (u+w>=r and 3*u+2*v+w>=3*r and u+2*v+3*w>=3*r
            and v+u//2+w//2>=r)


def full_klein4(supply, r):
    u,v,w = supply
    return min(u+v,u+w,v+w)>=r


def histograms(r, d):
    if d==1:
        yield ()
    else:
        for a in range(r+1):
            for tail in histograms(r-a,d-1):
                yield (a,)+tail


def plus(kind,a,b):
    return (a+b)%4 if kind=='C4' else a^b


def oracle(kind, r):
    @lru_cache(None)
    def reachable(supply):
        if not any(supply): return frozenset({(0,0,0)})
        a=next(i+1 for i,x in enumerate(supply) if x)
        prev=list(supply); prev[a-1]-=1
        old=reachable(tuple(prev)); ans=set(old)  # put new item in reserve
        for h in old:
            counts=(r-sum(h),)+h
            for b,number in enumerate(counts):
                if not number: continue
                c=plus(kind,a,b)
                new=list(h)
                if b: new[b-1]-=1
                if c: new[c-1]+=1
                ans.add(tuple(new))
        return frozenset(ans)
    return reachable


def compositions_bounded(n, counts):
    if len(counts)==1:
        if 0<=n<=counts[0]: yield (n,)
        return
    for a in range(min(n,counts[0])+1):
        for tail in compositions_bounded(n-a, counts[1:]):
            yield (a,)+tail


def fixed_quota_oracle(kind, counts, quotas):
    """Exhaustive colour-table search with exact block lengths; reserve last."""
    @lru_cache(None)
    def go(rem, qs):
        if not qs: return frozenset({()})
        out=set()
        for t in compositions_bounded(qs[0],rem):
            z=0
            for a,n in enumerate(t):
                for _ in range(n): z=plus(kind,z,a)
            left=tuple(x-y for x,y in zip(rem,t))
            for tail in go(left,qs[1:]): out.add((z,)+tail)
        return frozenset(out)
    return go(tuple(counts),tuple(quotas))


def patterns(add, d):
    """Unconditional general finite-group DP, using all short words.
    Zero-sum-free restriction is unnecessary for correctness of this DP."""
    out=[set() for _ in range(d)]
    for h in histograms(d-1,d):
        z=0
        for a,n in enumerate(h,1):
            for _ in range(n): z=add(z,a)
        out[z].add(h)
    return out


def support_dp(add,d,supply,targets):
    P=patterns(add,d)
    cap=tuple(min(x,(d-1)*len(targets)) for x in supply)
    reach={tuple(0 for _ in cap)}
    for t in targets:
        if t==0: continue
        next_set=set()
        for a in reach:
            for b in P[t]:
                c=tuple(x+y for x,y in zip(a,b))
                if all(x<=y for x,y in zip(c,cap)): next_set.add(c)
        reach=next_set
        if not reach: return False
    return True


def run():
    n=0; full=0; fixed=0
    for kind,test,cover in [('C4',cyclic4,full_cyclic4),('V4',klein4,full_klein4)]:
        for r in range(1,8):
            reach=oracle(kind,r)
            demands=list(histograms(r,4))
            for s in product(range(9),repeat=3):
                attainable=reach(s)
                for t in demands:
                    assert test(s,t)==(t in attainable),(kind,r,s,t)
                    n+=1
                assert cover(s,r)==(len(attainable)==len(demands)),(kind,r,s)
                full+=1
        print(f'{kind}: exhaustive supply coordinates 0..8, boxes 1..7: passed')
        rng=Random(2601127)
        for _ in range(100):
            r=rng.choice([1,2,3]); zeros=rng.randint(3*(r+1),3*(r+1)+5)
            s=tuple(rng.randrange(7) for _ in range(3)); m=zeros+sum(s)
            if m<9+3*r: continue
            cuts=[3]*r
            for _ in range(rng.randint(0,min(6,m-9-3*r))): cuts[rng.randrange(r)]+=1
            if m-sum(cuts)<9: continue
            reachable=fixed_quota_oracle(kind,(zeros,)+s,cuts)
            for t in product(range(4),repeat=r):
                dem=tuple(t.count(a) for a in (1,2,3))
                assert test(s,dem)==(t in reachable),(kind,s,cuts,t)
                assert support_dp(lambda x,y:plus(kind,x,y),4,s,t)==(t in reachable)
                fixed+=1
        print(f'{kind}: fixed-quota colour-table checks: passed')
    for r in range(1,24,2):
        s=(r,0,r)
        assert not full_cyclic4(s,r)
        for t in histograms(r,4):
            assert cyclic4(s,t)==(t!=(0,r,0)),(r,t)
    print('Odd-r single-missing-pattern family r=1,3,...,23: passed')
    print(f'{n:,} exact support comparisons; {full:,} full-coverage comparisons; '
          f'{fixed:,} fixed-quota comparisons (also general DP).')

if __name__=='__main__': run()
