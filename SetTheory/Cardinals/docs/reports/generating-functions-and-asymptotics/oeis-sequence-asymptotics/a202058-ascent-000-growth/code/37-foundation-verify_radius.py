#!/usr/bin/env python3
"""Independent finite checks for the A202058 radius proof; not a proof substitute."""
import json, math, hashlib
from pathlib import Path
from functools import lru_cache
from collections import defaultdict

ROOT=Path(__file__).resolve().parent

def children(s,u,k):
    for i in range(s+u):
        if i<s: yield (s-1,u+(i>=k),i)
        else: yield (s+1,u-(i<k),i+1)

@lru_cache(None)
def forward_suffix(n,s,u,k):
    if n==0: return 1
    return sum(forward_suffix(n-1,*y) for y in children(s,u,k))

@lru_cache(None)
def paper_suffix(n,a,l,s):
    if n==0:return 1
    return (sum(paper_suffix(n-1,a+(i>l)-1,i-1,s-1) for i in range(s))
          +sum(paper_suffix(n-1,a+(i>l),i,s+1) for i in range(s,a+2)))

def brute(N):
    words=[((0,),0,{0:1})]
    counts=[1,1]
    for n in range(2,N+1):
        nxt=[]
        for w,asc,mult in words:
            for i in range(asc+2):
                if mult.get(i,0)==2:continue
                mm=mult.copy();mm[i]=mm.get(i,0)+1
                nxt.append((w+(i,),asc+(i>w[-1]),mm))
        words=nxt;counts.append(len(words))
    return counts

known=[1,1,2,4,10,27,83,277,1015,4007,17047,77451,374889,1923168,
       10427250,59544957,357236992,2245822801,14762969601,101264286082,
       723499803180]
seq=[1]+[forward_suffix(n-1,1,1,1) for n in range(1,len(known))]
paper=[1]+[paper_suffix(n-1,0,0,1) for n in range(1,len(known))]
assert seq==known==paper
assert brute(10)==known[:11]

qvals=[0.000001,.001,.01,.1,.5,1,2,4,8,12,20,40,80]
max_residual_ratio=(0,None)
max_rank_shift=(0,None)
max_dup_rank=(0,None)
max_quad_ratio=(0,None)
tested=0
for q in qvals:
    em=math.exp(-q)
    p=(q+math.log(2-em))/2
    R=2-em
    A=math.exp(q-p)*(1-em)
    B=math.exp(p)*(1-em)
    qp=B/q
    C=8*(1+q)*math.exp(5*q/8)
    for m in range(1,41):
        for s in range(m):
            u=m-s
            D=s+R*u
            for k in range(m):
                r=(min(k,s)+R*max(k-s,0))/D
                dr=(-k*u if k<=s else -s*(m-k))/(D*D)
                lam=A*D/q
                deriv=lam-qp*(r+q*em*dr)
                total=0.;frozen=0.
                for i,y in enumerate(children(s,u,k)):
                    ss,uu,kk=y
                    assert ss>=0 and uu>=1 and 0<=kk<ss+uu
                    DD=ss+R*uu
                    rr=(min(kk,ss)+R*max(kk-ss,0))/DD
                    ri=(min(i,s)+R*max(i-s,0))/D
                    slow=p*(ss-s)+q*(uu-u)
                    exact=math.exp(slow+q*(r-rr))
                    frz=math.exp(slow+q*(r-ri))
                    total+=exact;frozen+=frz
                    shift=abs(rr-ri)*D
                    assert shift<=4+1e-11
                    if shift>max_rank_shift[0]:max_rank_shift=(shift,[q,m,s,k,i])
                    if i<s and i>=k:
                        d=r-rr
                        assert d<=1/8+1e-11
                        if d>max_dup_rank[0]:max_dup_rank=(d,[q,m,s,k,i])
                    else:
                        assert rr+1e-11>=ri
                    assert exact<=math.sqrt(2)*math.exp(5*q/8)*(1+1e-10)
                quad=abs(frozen-lam)/(3*math.sqrt(2)*math.exp(q/2))
                # Near q=0 cancellation in A/q is handled by tolerance.
                assert quad<=1+1e-7
                if quad>max_quad_ratio[0]:max_quad_ratio=(quad,[q,m,s,k])
                ratio=abs(deriv-total)/C
                assert ratio<=1+1e-7
                if ratio>max_residual_ratio[0]:max_residual_ratio=(ratio,[q,m,s,k])
                tested+=1

import mpmath as mp
mp.mp.dps=70
T=mp.quad(lambda y:2*mp.log((y*y+1)/2)/(y*y-1),[1,2,10,mp.inf])
Texact=3*mp.pi**2/8
assert abs(T-Texact)<mp.mpf('1e-65')
out={
 'scope':'Finite checks only; the radius proof is analytic.',
 'recurrence_terms_checked':len(known),
 'brute_force_through_n':10,
 'state_parameter_cases':tested,
 'q_values':qvals,
 'max_m':40,
 'max_residual_over_claimed_bound':max_residual_ratio,
 'max_rank_shift_times_D':max_rank_shift,
 'max_duplicate_ascent_extra_rank':max_dup_rank,
 'max_quadrature_over_claimed_bound':max_quad_ratio,
 'T_integral':str(T),
 'T_3pi2over8':str(Texact),
 'mu':str(1/Texact),
 'article_sha256':hashlib.sha256((ROOT/'a202058-report.tex').read_bytes()).hexdigest(),
}
(ROOT/'verify_radius.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
