#!/usr/bin/env python3
"""Independent finite checks of the alphabetic capacity theorem.

The mathematical proof is in report_section.tex. The Catalan recursion is
an independent finite sanity check, not a substitute for that proof.
"""
from functools import cache
from itertools import product
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent

def linear_capacity(cs):
    if len(cs)==1:return cs[0]
    if any(c<0 for c in cs):return -1
    total=0;slack=[]
    for k,c in enumerate(cs[:-1],1):total+=c;slack.append(total-k)
    return max(-1,min(slack))

@cache
def catalan_capacity(cs):
    if len(cs)==1:return cs[0]
    best=-1
    for k in range(1,len(cs)):
        a,b=catalan_capacity(cs[:k]),catalan_capacity(cs[k:])
        if a>=1 and b>=0:best=max(best,a-1)
    return best

def construct(cs,r):
    assert 0<=r<=linear_capacity(cs)
    if len(cs)==1:return 0,[0]
    debt=len(cs)-1;run=[]
    for i,c in enumerate(cs):
        u=min(c-(r if i==0 else 0),debt);run.append(u);debt-=u
    assert debt==0
    stack=[]
    for i in range(len(cs)-1,-1,-1):
        stack.append(i)
        for _ in range(run[i]):
            left,right=stack.pop(),stack.pop();stack.append((left,right))
    assert len(stack)==1
    return stack[0],run

def evaluate(t,cs):
    if isinstance(t,int):return cs[t]
    a,b=evaluate(t[0],cs),evaluate(t[1],cs)
    return a-1 if a>=1 and b>=0 else -1

def leaves(t):
    if isinstance(t,int):return [t]
    return leaves(t[0])+leaves(t[1])

def main():
    cases=valid=constructions=0;by_length=[]
    for n in range(1,8):
        count=0
        for cs in product(range(-1,4),repeat=n):
            a=linear_capacity(cs);b=catalan_capacity(cs)
            assert a==b,(cs,a,b)
            cases+=1;count+=1
            if a>=0:
                valid+=1
                for r in range(a+1):
                    t,run=construct(cs,r)
                    assert leaves(t)==list(range(n))
                    assert evaluate(t,cs)>=r
                    assert sum(run)==n-1
                    assert all(sum(run[:k])>=k for k in range(1,n))
                    assert all(v<=c-(r if i==0 else 0)for i,(v,c)in enumerate(zip(run,cs)))
                    constructions+=1
        by_length.append({'length':n,'capacity_vectors':count})
    out={'status':'PASS','vectors':cases,'feasible_vectors':valid,'constructed_tree_tests':constructions,'domain':{'lengths':[1,7],'capacities':[-1,0,1,2,3]},'by_length':by_length,'comparison':'Exact Catalan recursion over all binary parenthesizations versus linear prefix formula; all feasible incoming capacities reconstructed and independently evaluated.','scope':'Finite check supporting the separate ordinary mathematical theorem; no proof-assistant or binary-machine correctness claim.'}
    (HERE/'evidence/capacity-check-result.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
