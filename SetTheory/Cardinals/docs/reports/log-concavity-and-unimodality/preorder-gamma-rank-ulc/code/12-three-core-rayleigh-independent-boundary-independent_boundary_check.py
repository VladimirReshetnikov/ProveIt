#!/usr/bin/env python3
"""Independent exhaustive coefficient check using direct support enumeration.

No producer functions are imported. Matching supports are obtained by adjoining
disjoint physical arcs and deduplicating ordered endpoint masks. Coefficients
are recovered from exact base-3 encodings of formal vertex-role monomials.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib,json,time

OUT=Path(__file__).resolve().parent

def supports(arcs):
    out={(0,0)}
    for tail,head in arcs:
        endpoints=(1<<tail)|(1<<head)
        for S,T in tuple(out):
            if (S|T)&endpoints==0:
                out.add((S|(1<<tail),T|(1<<head)))
    return out

def monomial(S,T,powers,n):
    return sum(powers[v] for v in range(n) if S>>v&1)+sum(powers[n+v] for v in range(n) if T>>v&1)

def case(ci,j,k,exterior_tails):
    m=len(exterior_tails);n=3+m
    total=[2,1,1]+([1]*4 if m==4 else [2,1,1])
    tails=[ci,j,k]+list(exterior_tails)
    heads=[d-t for d,t in zip(total,tails)]
    assert sum(tails)==sum(heads)==4
    powers=[3**i for i in range(2*n)]
    target=sum(tails[v]*powers[v]+heads[v]*powers[n+v] for v in range(n))
    # Different arc ordering from producer: enumerate actual tail/head labels.
    possible=[(a,b) for a in range(n) for b in range(n)
              if (a<3)!=(b<3) and tails[a]>0 and heads[b]>0]
    histogram=Counter()
    support_total=0
    for graph in range(1<<len(possible)):
        arcs=[e for h,e in enumerate(possible) if graph>>h&1]
        family=supports(arcs)
        support_total+=len(family)
        classes=[set() for _ in range(8)]
        for S,T in family:
            classes[(S|T)&7].add(monomial(S,T,powers,n))
        positive=sum(target-a in classes[5] for a in classes[3])
        negative=sum(target-a in classes[7] for a in classes[1])
        coefficient=positive-negative
        if coefficient<0:
            raise AssertionError({'core':[ci,j,k],'exterior_tails':exterior_tails,
                                  'arcs':arcs,'positive':positive,'negative':negative})
        histogram[coefficient]+=1
    return {'core':[ci,j,k],'exterior_types':list(exterior_tails),
            'potential_arcs':len(possible),'graphs':1<<len(possible),
            'coefficient_histogram':dict(sorted(histogram.items())),
            'enumerated_support_instances':support_total}

def main():
    start=time.monotonic();cases=[]
    for ci,j,k in product(range(3),range(2),range(2)):
        et=4-ci-j-k
        cases.append(case(ci,j,k,[1]*et+[0]*(4-et)))
        for ts in product(range(3),range(2),range(2)):
            if ci+j+k+sum(ts)==4:
                cases.append(case(ci,j,k,ts))
    four=[c for c in cases if len(c['exterior_types'])==4]
    three=[c for c in cases if len(c['exterior_types'])==3]
    result={'verdict':'PASS','proof_scope':'Coefficientwise b_01*b_02-a_0*c for every finite three-core bipartite physical relation',
            'method':'Independent direct physical support enumeration and exact base-3 role-monomial coefficients',
            'monomial_types':len(cases),'graph_cases':sum(c['graphs'] for c in cases),
            'four_exterior_types':len(four),'four_exterior_graphs':sum(c['graphs'] for c in four),
            'three_exterior_types':len(three),'three_exterior_graphs':sum(c['graphs'] for c in three),
            'enumerated_support_instances':sum(c['enumerated_support_instances'] for c in cases),
            'coefficient_min':min(min(c['coefficient_histogram']) for c in cases),
            'coefficient_max':max(max(c['coefficient_histogram']) for c in cases),
            'elapsed_seconds':round(time.monotonic()-start,3),'cases':cases}
    (OUT/'independent_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))

if __name__=='__main__':main()
