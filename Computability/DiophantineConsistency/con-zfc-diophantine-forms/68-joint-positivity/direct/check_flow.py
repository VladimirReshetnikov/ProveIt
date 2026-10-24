#!/usr/bin/env python3
"""Independent finite regressions for the abstract flow theorem. Not a proof."""
from itertools import combinations_with_replacement, combinations, product
from collections import Counter
import json

F=range(3)
premises=[()] + [(i,) for i in F] + list(combinations_with_replacement(F,2))
rules=[(p,c) for p in premises for c in F]

def closure(rs):
    d=set()
    while True:
        n=d|{c for p,c in rs if all(a in d for a in p)}
        if n==d:return d
        d=n

def balances(rs,ns):
    v=[0]*3
    for (p,c),n in zip(rs,ns):
        v[c]+=n
        for a in p:v[a]-=n
    return v

cases=certificates=dominance=0
# Exhaust all systems of at most three distinct rules and all multiplicities 0..2.
for k in range(4):
    for rs in combinations(rules,k):
        d=closure(rs)
        for ns in product(range(3),repeat=k):
            v=balances(rs,ns)
            N=sum(ns); M=sum(n*len(p) for (p,c),n in zip(rs,ns))
            for t in F:
                cases+=1
                unit=[int(j==t) for j in F]
                if v==unit:
                    certificates+=1
                    assert t in d
                if all(v[j]>=unit[j] for j in F):
                    dominance+=1
                    assert t in d
                h=[v[j]-unit[j] for j in F]
                B=2+N+M
                assert (sum(h[j]*B**j for j in F)==0)==(h==[0]*3)
                if N==M+1:
                    B=max(2,N)
                    assert (sum(h[j]*B**j for j in F)==0)==(h==[0]*3)
# Invalid too-small radix: axiom 0 twice, one rule (1,1)->2, target1.
rs=[((),0),((1,1),2)];ns=[2,1]
v=balances(rs,ns);h=[v[j]-int(j==1) for j in F]
assert 1 not in closure(rs) and sum(h)==0 and sum(h[j]*2**j for j in F)==0
# Multiple conclusions invalidate the theorem: a -> a,t has balance e_t.
assert [1-1,1-0]==[0,1]
# Negative multiplicities invalidate it: axiom a minus (t -> a) gives e_t.
assert balances([((),0),((1,),0)],[1,-1])==[0,1,0]
result={'status':'pass','systems_rule_universe':len(rules),'target_flow_checks':cases,
        'exact_certificates':certificates,'dominating_certificates':dominance,
        'negative_controls':['too-small radix despite scalar conservation','multiple conclusions','negative multiplicity'],
        'scope':'finite regressions, not unbounded theorem verification'}
print(json.dumps(result,indent=2))
