#!/usr/bin/env python3
"""Finite consistency tests for the multicolor region bookkeeping, not an unbounded proof.
No NFA census and no external numerical libraries.
"""
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import json,random,time,hashlib
ROOT=Path(__file__).resolve().parent
START=time.time()
stats={'mixed_parameter_cases':0,'same_length_circulation_cases':0,'guard_transfer_cases':0,
       'charge_subinterval_cases':0,'periodic_residual_cases':0,'two_window_intersection_cases':0,
       'length_gate_cases':0}

# All hard-regime parameter pairs through n=240; the worst permitted common
# intersection size suffices because the mixed rank bound decreases with b.
for n in range(6,241):
    for j in range(n//2+1,n):
        for k in range(j+1,n+1):
            if gcd(j,k)!=1:continue
            lower=2*j+k-2*n
            if lower<=2:
                assert 2*j*k+1<=4*j*(n+1-j)+1<=(n+1)**2+1<=n*n+8*n
            b=max(3,lower)
            if b<=j:
                mu=F(k-b+2,k)
                assert 0<=F(j-b+2,j)<=mu<=1
                assert 2*mu*j*k+5*n+1<=4*j*(n-j+1)+5*n+1<=n*n+7*n+2<=n*n+8*n
            stats['mixed_parameter_cases']+=1
            # Exact unique length decomposition for three equally long cycles.
            for ell in (j,k):
                solutions=[]
                for a in range(3*ell//j+1):
                    rest=3*ell-a*j
                    if rest>=0 and rest%k==0:solutions.append((a,rest//k))
                assert solutions==([(3,0)] if ell==j else [(0,3)])
                stats['same_length_circulation_cases']+=1

for s in range(2,1001):
    for c in range(1,s):
        assert (s-c)+2*s+c*c+8*c<=s*s+8*s
        # Even allowing two unnecessary partition-boundary cuts still fits.
        assert (s-c)+2*s+2+c*c+8*c<=s*s+8*s
        stats['guard_transfer_cases']+=1

# Abstract common-anchor regions: every equal region has three constant-letter
# branches of the same length; the one unequal region is licensed singletonwise.
# Worst-case ternary targets change at every within-region adjacency. This gives
# the maximum conservative fragment count without enumerating exponentially many
# equivalent target words. Check every interval, including truncated regions.
rng=random.Random(20261001)
for trial in range(500):
    b=rng.randrange(3,8)
    short=[rng.randrange(1,5) for _ in range(b)]
    special=rng.randrange(b);delta=rng.randrange(1,6)
    long=short.copy();long[special]+=delta
    j=sum(short);k=sum(long);mu=F(k-b+2,k)
    assert sum(short)-b+2<=j and sum(long)-b+2<=k
    def lap(lengths,lap_id):
        ans=[]
        for region,t in enumerate(lengths):
            unequal=region==special
            for pos in range(t):
                charge=(1+int(pos==0)) if unequal else int(pos>0)
                ans.append((lap_id,region,unequal,charge))
        return ans
    alpha=rng.randrange(0,4);beta=rng.randrange(0,4)
    if alpha+beta==0:alpha=1
    tokens=[]
    for a in range(alpha):tokens+=lap(short,('j',a))
    split=len(tokens)
    for a in range(beta):tokens+=lap(long,('k',a))
    M=len(tokens)
    charges=[0]
    for tok in tokens:charges.append(charges[-1]+tok[-1])
    forced=[0]*(M+1)
    for i in range(1,M):
        left,right=tokens[i-1],tokens[i]
        cut=left[2] or right[2] or (left[:2]==right[:2])
        forced[i+1]=forced[i]+int(cut)
    for start in range(M):
        for end in range(start+1,M+1):
            worst_pieces=1+forced[end]-forced[start+1]
            charge=charges[end]-charges[start]
            assert worst_pieces<=charge+1,(trial,start,end,worst_pieces,charge)
            stats['charge_subinterval_cases']+=1
            if end<=split or start>=split:
                # n is replaced by k, an even tighter residual bound in this
                # abstract two-block model.
                assert charge<=mu*(end-start)+k
                stats['periodic_residual_cases']+=1
    # Exhaust every pair of disjoint prefix/suffix boundary windows; verify the
    # key bound of at most three intersections with two consecutive blocks.
    for e in range(M//2+1):
        if not e:continue
        windows=[(0,e),(M-e,M)]
        blocks=[(0,split),(split,M)]
        count=sum(max(a,c)<min(d,f) for a,d in windows for c,f in blocks)
        assert count<=3
        stats['two_window_intersection_cases']+=1

# Independent exact walk reachability on the gate, compared with its numerical
# semigroup expression and the asserted last exceptional length.
for m in range(2,101):
    limit=(m-1)**2+3*m
    semigroup=[False]*(limit+1);semigroup[0]=True
    for N in range(1,limit+1):
        semigroup[N]=(N>=m and semigroup[N-m]) or (N>=m-1 and semigroup[N-(m-1)])
    reachable=1;missing=[]
    for N in range(limit+1):
        actual=bool(reachable&1)
        expected=N==0 or (N>=m and semigroup[N-m])
        assert actual==expected
        if N>0 and not actual:missing.append(N)
        new=0
        for state in range(m):
            if reachable>>state&1:
                new|=(1<<(state+1)) if state<m-1 else 3
        reachable=new
    assert missing[-1]==(m-1)**2
    stats['length_gate_cases']+=1

result={'all_passed':True,'tests':stats,'parameter_n_max':240,'guard_s_max':1000,
        'abstract_region_models':500,'gate_m_range':[2,100],
        'scope':'Finite exact consistency checks; not an exhaustive ternary NFA census or a replacement for the proof',
        'seconds':round(time.time()-START,3),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'article_sha256':hashlib.sha256((Path(__file__).resolve().parent.parent/'hamiltonian-rank.tex').read_bytes()).hexdigest()}
(ROOT/'ternary_bookkeeping_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
