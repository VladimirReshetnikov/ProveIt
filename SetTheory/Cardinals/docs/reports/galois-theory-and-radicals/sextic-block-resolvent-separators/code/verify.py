#!/usr/bin/env python3
"""Exact checks for Finite Separators for Sextic Block Resolvents.

Standard-library arithmetic checks are independent of symbolic algebra.
SymPy is used only for the separately reported universal local identities.
This is a verifier/prototype on supplied exact roots, not an extracted
coefficient-only radical-solvability solver and not a Lean proof.
"""
from __future__ import annotations
from itertools import combinations
from math import prod
from pathlib import Path
import json

Pair = tuple[int, int]
Matching = tuple[Pair, Pair, Pair]
TriplePartition = tuple[tuple[int, int, int], tuple[int, int, int]]

def matchings(items: tuple[int, ...]) -> list[tuple[Pair, ...]]:
    if not items:
        return [()]
    a, rest = items[0], items[1:]
    return [(tuple(sorted((a,b))),) + m for b in rest
            for m in matchings(tuple(x for x in rest if x != b))]

MATCHINGS = tuple(sorted(matchings(tuple(range(6)))))
TRIPLES = tuple((b, tuple(i for i in range(6) if i not in b))
                for b in combinations(range(6), 3) if 0 in b)
EDGES = tuple(combinations(range(6), 2))
SHARED = tuple((i,j) for i,j in combinations(range(15),2)
               if set(MATCHINGS[i]) & set(MATCHINGS[j]))
DISJOINT = tuple((i,j) for i,j in combinations(range(15),2)
                 if not set(MATCHINGS[i]) & set(MATCHINGS[j]))
PAIR_PAIRS = tuple((a,b) for a,b in combinations(EDGES,2) if not set(a)&set(b))

def validate_roots(roots):
    if len(roots) != 6 or len(set(roots)) != 6:
        raise ValueError('Exactly six distinct roots are required.')

def pair_data(roots, matching):
    sums = [roots[i]+roots[j] for i,j in matching]
    products = [roots[i]*roots[j] for i,j in matching]
    a = sum(products)
    b = sum(sums[i]*products[j] for i in range(3) for j in range(3) if i != j)
    c = sum(products[i]*products[j] for i,j in combinations(range(3),2))
    return (a,b,c)

def triple_data(roots, partition):
    a = sum(roots[i]*roots[j] for block in partition for i,j in combinations(block,2))
    b = sum(prod(roots[i] for i in block) for block in partition)
    return a,b

def pair_values(roots, t):
    return tuple(a*t*t+b*t-c for a,b,c in (pair_data(roots,p) for p in MATCHINGS))

def triple_values(roots, t):
    return tuple(a*t-b for a,b in (triple_data(roots,p) for p in TRIPLES))

def separator(roots, bound=196):
    validate_roots(roots)
    for t in range(1,bound+1):
        if len(set(pair_values(roots,t)))==15 and len(set(triple_values(roots,t)))==10:
            return t
    raise AssertionError('The theorem predicts a separator in this range.')

def obstruction_parts(roots,t):
    h = pair_values(roots,t)
    q = prod(t*t+(roots[i]+roots[j])*t-roots[i]*roots[j] for i,j in EDGES)
    u = prod(h[i]-h[j] for i,j in DISJOINT)
    ell = prod((roots[a[0]]+roots[a[1]]-roots[b[0]]-roots[b[1]])*t
               -(roots[a[0]]*roots[a[1]]-roots[b[0]]*roots[b[1]])
               for a,b in PAIR_PAIRS)
    return q,u,ell

def discriminant(values):
    return prod((a-b)**2 for a,b in combinations(values,2))

def resolvent_coefficients(values):
    """Ascending coefficients of product (Z-value), exactly."""
    out = [1]
    for value in values:
        nxt = [0]*(len(out)+1)
        for i,c in enumerate(out):
            nxt[i] -= value*c
            nxt[i+1] += c
        out=nxt
    return out

def check_at(roots,t):
    validate_roots(roots)
    h,k = pair_values(roots,t),triple_values(roots,t)
    delta=discriminant(roots)
    q,u,ell=obstruction_parts(roots,t)
    assert discriminant(h)==delta**6*q**6*u**2
    assert discriminant(k)==delta**3*ell**2
    assert (q*u*ell != 0)==(len(set(h))==15 and len(set(k))==10)
    for matching, value in zip(MATCHINGS,h):
        desc=prod(2*t*t-prod(t-roots[i] for i in block) for block in matching)
        # Value plus 2*t^2*h is independent of the matching.
        base=prod(2*t*t-prod(t-roots[i] for i in block) for block in MATCHINGS[0])
        assert desc+2*t*t*value == base+2*t*t*h[0]
    for partition,value in zip(TRIPLES,k):
        desc=prod(2*t*t-prod(t-roots[i] for i in block) for block in partition)
        base=prod(2*t*t-prod(t-roots[i] for i in block) for block in TRIPLES[0])
        assert desc+2*t*t*value == base+2*t*t*k[0]


def symbolic_checks():
    import sympy as sp
    r=sp.symbols('r0:6'); t,v=sp.symbols('t v')
    e1=sum(r);e2=sum(r[i]*r[j] for i,j in EDGES)
    f=prod(t-ri for ri in r)
    p=MATCHINGS[0];a,b,c=pair_data(r,p)
    desc=prod(v-prod(t-r[i] for i in block) for block in p)
    expanded=v**3-(3*t*t-e1*t+a)*v*v+(3*t**4-2*e1*t**3+(e2+a)*t*t-b*t+c)*v-f
    assert sp.expand(desc-expanded)==0
    p=TRIPLES[0];a,b=triple_data(r,p)
    desc=prod(v-prod(t-r[i] for i in block) for block in p)
    assert sp.expand(desc-(v*v-(2*t**3-e1*t*t+a*t-b)*v+f))==0
    i,j=SHARED[0]
    common=next(iter(set(MATCHINGS[i])&set(MATCHINGS[j])))
    ai,bi,ci=pair_data(r,MATCHINGS[i]);aj,bj,cj=pair_data(r,MATCHINGS[j])
    q=t*t+(r[common[0]]+r[common[1]])*t-r[common[0]]*r[common[1]]
    assert sp.expand((ai-aj)*t*t+(bi-bj)*t-ci+cj-(ai-aj)*q)==0
    # General exchange identity for triple partitions.
    a,b,c,d,e,f=r
    P=((0,1,2),(3,4,5)); Q=((0,1,3),(2,4,5))
    ap,bp=triple_data(r,P);aq,bq=triple_data(r,Q)
    assert sp.expand((ap-aq)*t-bp+bq-(c-d)*((a+b-e-f)*t-(a*b-e*f)))==0
    return {'pair_descriptor_expansion':True,'triple_descriptor_expansion':True,
            'shared_block_factorization':True,'triple_exchange_factorization':True}


def main():
    assert (len(MATCHINGS),len(TRIPLES),len(SHARED),len(DISJOINT),len(PAIR_PAIRS))==(15,10,45,60,45)
    # Each root transposition fixes no reversed edge of the disjoint-matching graph.
    for a,b in EDGES:
        perm=list(range(6));perm[a],perm[b]=perm[b],perm[a]
        action=[]
        for m in MATCHINGS:
            pm=tuple(sorted(tuple(sorted(perm[i] for i in block)) for block in m))
            action.append(MATCHINGS.index(pm))
        assert all(not (action[i]==j and action[j]==i) for i,j in DISJOINT)
    cases=[(-5,-2,0,1,4,9),(0,1,2,3,4,5),(-7,-3,2,5,11,19),(1,4,10,23,51,109)]
    exact_count=0
    for roots in cases:
        for t in range(0,17):
            check_at(roots,t);exact_count+=1
        for a,b in EDGES:
            perm=list(roots);perm[a],perm[b]=perm[b],perm[a]
            assert obstruction_parts(tuple(perm),23)==obstruction_parts(roots,23)
    histogram={}; maximum=0; maximizers=[]
    samples=list(combinations(range(-3,8),6))
    for roots in samples:
        t=separator(roots)
        histogram[t]=histogram.get(t,0)+1
        if t>maximum: maximum=t;maximizers=[roots]
        elif t==maximum:maximizers.append(roots)
    for t in range(1,21):
        roots=tuple(i*t for i in range(6))
        assert len(set(pair_values(roots,t)))<15
    lower_roots=(-3,0,1,2,3,4)
    lower_counts=[{'t': u, 'distinct_pair_values': len(set(pair_values(lower_roots,u))),
                   'distinct_triple_values': len(set(triple_values(lower_roots,u)))}
                  for u in range(1,9)]
    assert separator(lower_roots)==8
    chosen=(0,1,2,3,4,5);t=separator(chosen)
    output={'counts':{'pair_partitions':15,'triple_partitions':10,'shared_partition_pairs':45,
                      'disjoint_partition_pairs':60,'disjoint_root_pair_pairs':45},
            'symbolic_checks':symbolic_checks(),'exact_discriminant_checks':exact_count,
            'root_transposition_symmetry_checks':len(cases)*15,
            'exhaustive_root_sample':{'universe':list(range(-3,8)),'six_subsets':len(samples),
                'first_separator_histogram':histogram,'maximum_first_separator':maximum,
                'first_maximizer':maximizers[0]},
            'fixed_parameter_counterexamples_checked':20,
            'initial_interval_lower_bound':{'roots':lower_roots,'counts':lower_counts,
                'sorted_pair_values_at_8':sorted(pair_values(lower_roots,8)),
                'sorted_triple_values_at_8':sorted(triple_values(lower_roots,8))},
            'example':{'roots':chosen,'first_separator':t,
                       'pair_resolvent_ascending':resolvent_coefficients(pair_values(chosen,t)),
                       'triple_resolvent_ascending':resolvent_coefficients(triple_values(chosen,t))},
            'limitations':'Finite and local symbolic checks support, but do not replace, the written general proofs. No Lean execution. No complete coefficient-only solver is claimed.'}
    out=Path(__file__).resolve().parents[1]/'checks'/'verification.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__':
    main()
