#!/usr/bin/env python3
"""Independent literal endpoint-pair/Hall audit of universal-sink last inequality.
Uses integer activities, no matching-witness sums and no producer imports.
"""
from itertools import combinations
from math import prod
from random import Random
from fractions import Fraction
from pathlib import Path
import json, time
ROOT=Path(__file__).resolve().parent
rng=Random(100126)

def subsets(mask):
    out=[];s=mask
    while True:
        out.append(s)
        if not s: return out
        s=(s-1)&mask

def esym(a,k):
    if k<0:return 0
    e=[1]+[0]*k
    for x in a:
        for j in range(k,0,-1):e[j]+=x*e[j-1]
    return e[k]

def mp(mask,a):
    return prod(a[i] for i in range(len(a)) if mask>>i&1)

def full_hall(U,V,adj):
    # Hall on all nonempty subsets of tails, with literal full head mask.
    A=U
    while A:
        nbr=0;z=A
        while z:
            b=z&-z;i=b.bit_length()-1;nbr|=adj[i]&V;z-=b
        if nbr.bit_count()<A.bit_count():return False
        A=(A-1)&U
    return True

def arrangements(r,s):
    C=(1<<r)-1;n=r+s
    out=[]
    for U in range(1<<r):
        k=U.bit_count();avail=[i for i in range(n) if not U>>i&1]
        for vs in combinations(avail,k):out.append((U,sum(1<<i for i in vs),k))
    return out

def graph_from_code(r,code):
    edges=[(i,j) for i in range(r) for j in range(r) if i!=j]
    adj=[0]*r
    for k,(i,j) in enumerate(edges):
        if code>>k&1:adj[i]|=1<<j
    return adj

def direct_support(r,s,adj):
    W=((1<<s)-1)<<r
    return [(U,V,k) for U,V,k in arrangements(r,s) if full_hall(U,V,[a|W for a in adj])]

def direct_gamma(r,s,supp,x,y,w):
    a=y+w;g=[0]*(r+1)
    for U,V,k in supp:g[k]+=mp(U,x)*mp(V,a)
    return g

def proposed_top(r,adj,x,y,w):
    C=(1<<r)-1;p=prod(x);A=esym(x,r-1);B=esym(x,r-2)
    active=[any(adj[i]>>j&1 for i in range(r)) for j in range(r)]
    d=sum(y[j]*mp(C^(1<<j),x) for j in range(r) if active[j])
    c=0;b=0
    for i,j in combinations(range(r),2):
        U=C^(1<<i)^(1<<j);uu=[a for a in range(r) if U>>a&1]
        c+=mp(U,x)*(y[i]*any(adj[a]>>i&1 for a in uu)+y[j]*any(adj[a]>>j&1 for a in uu))
        # Explicit injection existence, separate implementation from full Hall.
        feasible=any(a!=z and adj[a]>>i&1 and adj[z]>>j&1 for a in uu for z in uu)
        if feasible:b+=mp(U,x)*y[i]*y[j]
    E=lambda k:esym(w,k)
    top=[B*E(r-2)+c*E(r-3)+b*E(r-4),A*E(r-1)+d*E(r-2),p*E(r)]
    # Division-free core and sink inequalities.
    assert (r-1)*A*A>=2*r*p*B
    assert A*d>=p*c
    assert d*d>=2*p*b
    assert (r-2)*E(r-1)*E(r-2)>=r*E(r-3)*E(r)
    assert (r-2)*(r-3)*E(r-2)**2>=r*(r-1)*E(r-4)*E(r)
    return top

counts={'graphs':0,'weighted_instances':0,'literal_supported_pairs':0,'positive_top':0,'zero_top':0,'positive_all_activities':0,'sharp_bound_checks':0,'sharp_equalities':0}
best=None;byrank={}
def check(r,s,adj,weights,label):
    global best
    supp=direct_support(r,s,adj)
    counts['graphs']+=1;counts['literal_supported_pairs']+=len(supp)
    for x,y,w in weights:
        g=direct_gamma(r,s,supp,x,y,w);t=proposed_top(r,adj,x,y,w)
        assert g[-3:]==t,(label,x,y,w,g,t)
        gap=(r-1)*g[-2]**2-2*r*g[-3]*g[-1]
        assert gap>=0,(label,x,y,w,g,gap)
        m=sum(z>0 for z in w)
        if m>=r:
            sharp_gap=(r-1)**2*(m-r+1)*g[-2]**2-2*r*r*(m-r+2)*g[-3]*g[-1]
            assert sharp_gap>=0,(label,'sharp',x,y,w,g,sharp_gap)
            counts['sharp_bound_checks']+=1
            if g[-1] and not sharp_gap:counts['sharp_equalities']+=1
        counts['weighted_instances']+=1
        counts['positive_top' if g[-1] else 'zero_top']+=1
        if min(x+y+w,default=1)>0:counts['positive_all_activities']+=1
        deg=max(k for k,z in enumerate(g) if z)
        key=f'core{r}/sinks{s}/degree{deg}'
        byrank[key]=byrank.get(key,0)+1
        if g[-3]*g[-1]:
            ratio=Fraction((r-1)*g[-2]**2,2*r*g[-3]*g[-1])
            if best is None or ratio<best[0]:best=(ratio,{'label':label,'x':x,'y':y,'w':w,'gamma':g})

start=time.time()
# Exhaust all loopless labelled cores on four vertices, with multiple distinct weights.
for code in range(1<<12):
    x=[rng.randrange(1,8) for _ in range(4)]; y=[rng.randrange(1,8) for _ in range(4)]
    w=[rng.randrange(1,8) for _ in range(4)]
    zero=([rng.randrange(4) for _ in range(4)],[rng.randrange(4) for _ in range(4)],[rng.randrange(4) for _ in range(4)])
    check(4,4,graph_from_code(4,code),[([1]*4,[1]*4,[1]*4),(x,y,w),zero],f'r4-code{code}')
# Larger ranks; edge density, zero values, and too few sinks are varied independently.
for r in range(4,9):
    for sample in range(70):
        s=r if sample<55 else sample%r
        density=[0,.05,.2,.5,.8,.95,1][sample%7]
        adj=[sum(1<<j for j in range(r) if i!=j and rng.random()<density) for i in range(r)]
        weights=[]
        for zero in (False,True):
            vals=lambda n:[rng.randrange(0 if zero else 1,7) for _ in range(n)]
            weights.append((vals(r),vals(r),vals(s)))
        check(r,s,adj,weights,f'r{r}-sample{sample}-s{s}')
# Sink counts strictly above the core size; literal Hall enumeration retained.
for r in range(4,7):
    for s in (r+1,r+2,r+3):
        for sample in range(8):
            adj=graph_from_code(r,0) if sample==0 else [sum(1<<j for j in range(r) if i!=j and rng.randrange(2)) for i in range(r)]
            weights=[([1]*r,[1]*r,[1]*s),([rng.randrange(1,9) for _ in range(r)],[rng.randrange(9) for _ in range(r)],[rng.randrange(9) for _ in range(s)])]
            check(r,s,adj,weights,f'r{r}-largesink{s}-sample{sample}')
receipt={'status':'PASS','elapsed_seconds':round(time.time()-start,3),'counts':counts,'by_rank_degree':byrank,'minimum_target_ratio':str(best[0]),'minimum_case':best[1],'seed':100126,'method':'literal disjoint endpoint pairs, full Hall subsets of tails; exact integer arithmetic; independent explicit two-head injection for proposed formula'}
(ROOT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2),flush=True)
