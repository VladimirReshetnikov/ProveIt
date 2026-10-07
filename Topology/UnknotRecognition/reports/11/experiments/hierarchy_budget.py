"""Finite-state progress budgets, not a topological hierarchy implementation."""
from math import comb,prod
from itertools import product
import json
from pathlib import Path


def mixed_radix(states, caps):
    if any(len(h)!=len(caps) or any(not 0<=x<=g for x,g in zip(h,caps)) for h in states):
        raise ValueError('out-of-range progress state')
    rank=[]
    for h in states:
        x=0
        for value,g in zip(h,caps): x=x*(g+1)+value
        rank.append(x)
    return rank


def budget_count(length,cap,support=None,total=None):
    if min(length,cap)<0: raise ValueError('negative parameters')
    if support is None and total is None: return (cap+1)**length
    # Joint support/mass constraints by coefficient DP.
    support=length if support is None else min(support,length)
    total=length*cap if total is None else min(total,length*cap)
    if min(support,total)<0: return 0
    dp={(0,0):1}
    for _ in range(length):
        new={}
        for (s,m),a in dp.items():
            for x in range(min(cap,total-m)+1):
                ss=s+(x>0)
                if ss<=support: new[ss,m+x]=new.get((ss,m+x),0)+a
        dp=new
    return sum(dp.values())


def main():
    count=0
    for length in range(5):
        for cap in range(4):
            states=list(product(range(cap+1),repeat=length))
            assert mixed_radix(states,[cap]*length)==list(range((cap+1)**length))
            for r in range(length+1):
                for g in range(length*cap+1):
                    actual=sum(sum(x>0 for x in h)<=r and sum(h)<=g for h in states)
                    assert budget_count(length,cap,r,g)==actual
                    count+=1
    report={'finite_parameter_checks':count,'failures':0,
            'scope':'finite progress-state counting only; no topological bound on L,g,r,G is asserted'}
    Path('results/hierarchy_budget_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report)

if __name__=='__main__': main()
