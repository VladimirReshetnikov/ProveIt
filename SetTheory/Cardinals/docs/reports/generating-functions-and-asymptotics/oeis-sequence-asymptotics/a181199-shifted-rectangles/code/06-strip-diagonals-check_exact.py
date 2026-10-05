#!/usr/bin/env python3
"""Exact, independent checks of shifted-strip event decomposition; stdlib only."""
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial
from fractions import Fraction
from pathlib import Path
import json

def binomial(N,K):
    if K < 0: return 0
    if N >= 0: return comb(N,K) if K <= N else 0
    return (-1)**K * comb(K-N-1,K)

def sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))

@lru_cache(None)
def kernel(a,b):
    k=len(a)
    assert len(b)==k
    out=0
    for p in permutations(range(k)):
        ds=[b[i]-a[p[i]] for i in range(k)]
        v=1
        for i,d in enumerate(ds): v *= binomial(sum(ds[i:]),d)
        out += sign(p)*v
    return out

def chamber_direct(a,b):
    if any(x>y for x,y in zip(a,b)): return 0
    @lru_cache(None)
    def go(x):
        if x==b:return 1
        z=0
        for i in range(len(x)):
            if x[i]>=b[i]:continue
            y=list(x);y[i]+=1
            if i and y[i]>=y[i-1]:continue
            z+=go(tuple(y))
        return z
    return go(a)

def cell_poset(m,n):
    N=m*n;full=(1<<N)-1
    pred=[0]*N
    for i in range(m):
        for j in range(n):
            u=i*n+j
            for x,y in ((i,j+1),(i+1,j),(i+1,j+1),(i+1,j-1)):
                if x<m and 0<=y<n: pred[x*n+y] |=1<<u
    @lru_cache(None)
    def go(mask):
        if mask==full:return 1
        return sum(go(mask|1<<u) for u in range(N)
                   if not mask>>u&1 and pred[u]&mask==pred[u])
    return go(0)

def state_paths(m,n):
    @lru_cache(None)
    def go(x):
        if x==(n,)*m:return 1
        ans=0
        for i in range(m):
            if x[i]==n:continue
            y=list(x);y[i]+=1
            if any(y[j]<y[j+1] or (0<y[j]==y[j+1]<n) for j in range(m-1)):continue
            ans+=go(tuple(y))
        return ans
    return go((0,)*m)

def dyck(m):
    def go(w,b,s):
        if s==m:yield w;return
        if b<m:yield from go(w+'B',b+1,s)
        if s<b:yield from go(w+'S',b,s+1)
    return list(go('',0,0))

def event_sum(m,n):
    if n<2:return 1
    endpoints={k:[tuple(reversed(c)) for c in combinations(range(1,n),k)] for k in range(m+1)}
    totals={}
    for w in dyck(m):
        @lru_cache(None)
        def go(j,a):
            if j==2*m:return int(a==())
            out=0;k=len(a)
            for b in endpoints[k]:
                if any(x>y for x,y in zip(a,b)):continue
                if w[j]=='B':
                    if k and b[-1]<2:continue
                    after=b+(1,)
                else:
                    if not k or b[0]!=n-1:continue
                    after=b[1:]
                out+=kernel(a,b)*go(j+1,after)
            return out
        totals[w]=go(0,())
    return sum(totals.values()),totals

def kernel_factorial(a,b):
    L=sum(b)-sum(a)
    if L<0:return 0
    out=Fraction(0)
    for p in permutations(range(len(a))):
        ds=[b[i]-a[p[i]] for i in range(len(a))]
        if any(d<0 for d in ds):continue
        v=Fraction(factorial(L))
        for d in ds:v/=factorial(d)
        out+=sign(p)*v
    assert out.denominator==1
    return int(out)

def run():
    rows=[]
    for m in range(1,7):
        for n in range(0,9):
            a=cell_poset(m,n);b=state_paths(m,n)
            assert a==b,(m,n,a,b)
            r={'m':m,'n':n,'cell_poset':a,'state_paths':b}
            if m<=4 and n<=7 or m<=6 and n<=5:
                e=event_sum(m,n);v=e if isinstance(e,int) else e[0]
                assert v==a,(m,n,'event',v,a)
                r['event_sum']=v
                if (m,n) in ((2,4),(3,4),(4,4),(5,5)) and n>=2:r['event_word_totals']=e[1]
            if m==2 and n>=1:assert a==comb(2*n-2,n-1)//n
            rows.append(r)
    cases=0
    for k in range(0,5):
        xs=[tuple(reversed(c)) for c in combinations(range(-1,6),k)]
        for a,b in product(xs,repeat=2):
            v=kernel(a,b);z=chamber_direct(a,b);f=kernel_factorial(a,b)
            assert v==z==f,(a,b,v,z,f)
            cases+=1
    binomial_cases=0
    for k in range(1,5):
        for ds in product(range(-2,4),repeat=k):
            v=1
            for i,d in enumerate(ds):v*=binomial(sum(ds[i:]),d)
            if any(d<0 for d in ds):assert v==0
            else:
                f=factorial(sum(ds))
                for d in ds:f//=factorial(d) # sequential divisions are exact for multinomials
                assert v==f,(ds,v,f)
            binomial_cases+=1
    areas={}
    for m in range(1,10):
        sums=[]
        for w in dyck(m):
            k=0;a=0
            for c in w:a+=k;k+=1 if c=='B' else -1
            sums.append(a)
        assert max(sums)==m*m
        areas[m]={'dyck_words':len(sums),'max_pre_event_coordinates':max(sums)}
    result={'passed':True,'cell_state_instances':len(rows),'event_instances':sum('event_sum' in r for r in rows),'kernel_instances':cases,'binomial_product_instances':binomial_cases,'dyck_bounds':areas,'records':rows}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k not in ('records','dyck_bounds')})
if __name__=='__main__':run()
