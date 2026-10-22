#!/usr/bin/env python3
"""Audit strict windows as a filtered subset of the already enumerated T4 list.

Reads JSON only; does not import the new compiler or upstream generators.
"""
from pathlib import Path
from collections import Counter
import json

ROOT=Path(__file__).resolve().parents[1]
old=json.loads((ROOT/'reference/t4_windows.json').read_text())
new=json.loads((ROOT/'data/strict_windows.json').read_text())
data=json.loads((ROOT/'data/strict_compiler_checks.json').read_text())['scalars']
L,Q,R,V,H=434,435,436,437,438
phases={L,Q,R}; allowed={(L,L),(L,Q),(Q,R),(R,R)}
S=(L,Q,R,1); E=(H,0,0,H)

def require(v,msg):
    if not v: raise ValueError(msg)

def head(x):
    if x==Q:return 0
    if x<434 and x>=2:return x//2-1
    return None

def strict_filter(w):
    left,c,right,n=w
    for x,y in ((left,c),(c,right)):
        if x==V or y==V:
            if x==V and y==V:return False
            if x==V and y in phases and y!=L:return False
            if y==V and x in phases and x!=R:return False
        else:
            if (x==H)!=(y==H):return False
            if (x in phases)!=(y in phases):return False
            if x in phases and (x,y) not in allowed:return False
    if V in (left,c,right) and any(x not in {0,L,R,V,H} for x in (left,c,right)):
        return False
    if n==H and (any(x in phases for x in (left,c,right)) or
                  any(head(x) not in (None,215) for x in (left,c,right))):
        return False
    if c==H:
        if left==V and n!=L:return False
        if right==V and n!=R:return False
    return True

oldset={tuple(w) for w in old}
newset={tuple(w) for w in new}
filtered={w for w in oldset if strict_filter(w)}
require(len(new)==len(newset)==5252,'new census')
require(tuple(new[0])==S and tuple(new[1])==E,'selectors')
require(newset<=oldset,'new windows not an old T4 subset')
require(filtered==newset-{E},'independent filter census')
require(E not in filtered,'forbidden window surviving strict filter')
require(new[2:]==sorted([list(w) for w in filtered if w!=S]),'canonical order')

# Reconstruct every native support point and check the modified anchors.
k=5252; a=439; nd=2; M=11839; Hc=226259; T1=487157; T2=747619; cell=1953125
coords=((1,0),(1,1),(1,2),(2,1))
def ex(rc,s):
    r,c=rc; return k+3*a+(2-r)*3*a+(2-c)*a+s
copy={ex(rc,s) for rc in coords for s in range(a)}
anchors={M,3*M,5*M,11*M}; dummy={k+12*a,k+12*a+1}
support=set(range(k))|copy|anchors|dummy
require(len(support)==7014 and max(support)==11*M,'support count')
require({(5*M-x)%cell for x in support}&{(11*M-x)%cell for x in support}=={0},'anchor alignment')
require({(T1-x)%cell for x in support|{k+12*a+1}}.isdisjoint(
    {(T2-x)%cell for x in support|{k+12*a+1}}),'clause separation')
ell=13;p=1075;m=7013
popmu=ell-1+(4*a+4+p)
require(popmu==2847 and 2*popmu+3*a+2==m,'population identity')
require((T2-T1)%4==2,'band cancellation')
bare=(3*a,Hc+a,4*M,8*M)
dc=sum(pow(2,x,5) for x in bare)%5
require((2*dc-pow(2,Hc,5))%5==3,'rank tuning unit')
receipt=dict(status='PASS',old_T4_windows=len(oldset),strict_windows=len(filtered),
    selectors_including_forbidden=len(new),subset_check=True,independent_filter_check=True,
    canonical_order=True,strict_center_counts=dict(Counter(w[1] for w in filtered)),
    native_support=len(support),dummy_count=2,mu_population=popmu,
    total_high_mask_population=m+1,low_mask_population=f'd-{m+1}',
    anchor_alignment=True,clause_separation=True,mod5_unit=3,
    scope='Independent finite subset/order/support/population audit; unbounded semantic implications are in STRICT_COMPILER_REVIEW.md.')
(ROOT/'data/strict_independent_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='strict_center_counts'},indent=2))
