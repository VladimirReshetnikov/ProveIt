#!/usr/bin/env python3
"""Reproduce the exact finite checks; no third-party packages or network needed."""
from __future__ import annotations
import csv
import json
from itertools import combinations_with_replacement, product
from math import prod, comb
from pathlib import Path
import sys
from mixed_radix import (
    construct, carry_basis, degree, coordinates, numerator, sumset_size,
    binomial_size, eventual_size, compositions, relation_generators_at,
    exact_rank, canonical_representation, min_summands, short_vectors,
)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'


def main() -> None:
    DATA.mkdir(exist_ok=True)
    profiles = [q for r in range(1,5)
                for q in combinations_with_replacement(range(2,7), r)]
    count_rank_checks = count_generators = count_multisets = 0
    rows = []
    for q in profiles:
        a = construct(q)
        for j, v in enumerate(carry_basis(q)):
            assert degree(v) == q[j]
            assert not sum(v)
            assert not sum(x*y for x, y in zip(v,a))
            assert coordinates(q,v) == tuple(int(i==j) for i in range(len(q)))
        for h in range(max(q)+1):
            relations, multiset_count, distinct = relation_generators_at(a,h)
            actual = exact_rank(relations)
            expected = sum(x <= h for x in q)
            assert actual == expected, (q,h,actual,expected)
            assert distinct == sumset_size(q,h) == binomial_size(q,h)
            for c in relations:
                coeff = coordinates(q,c)
                assert degree(c) <= h
                assert all(z==0 for x,z in zip(q,coeff) if x>h)
            count_generators += len(relations)
            count_multisets += multiset_count
            count_rank_checks += 1
            rows.append({'radices':','.join(map(str,q)), 'h':h, 'rank':actual,
                         'multisets':multiset_count, 'sumset_size':distinct,
                         'collision_generators':len(relations)})

    # Stronger theorem: every ordering of the radices is allowed. Neither this
    # rank calculation nor the collision enumeration uses the carry bound.
    unordered_profiles = [q for r in range(1,5) for q in product(range(2,6), repeat=r)]
    unordered_rank_checks = unordered_generators = unordered_multisets = 0
    for q in unordered_profiles:
        a=construct(q)
        for h in range(max(q)+1):
            relations,multisets,distinct=relation_generators_at(a,h)
            assert exact_rank(relations)==sum(x<=h for x in q)
            assert distinct==sumset_size(q,h)==binomial_size(q,h)
            for c in relations:
                z=coordinates(q,c)
                assert all(x*abs(zj)<=degree(c) for x,zj in zip(q,z))
            unordered_generators+=len(relations)
            unordered_multisets+=multisets
            unordered_rank_checks+=1

    # Exhaustive vector-ball comparison. All pairs in each sum bucket are used,
    # so every degree <=H relation appears (pad with zero summands).
    vector_ball_cases=[]
    for q in [(2,3),(3,2),(2,2,3),(4,2,3),(3,3)]:
        a=construct(q); h=max(q)+1
        buckets={}
        for rep in compositions(h,len(a)):
            n=sum(x*y for x,y in zip(rep,a))
            buckets.setdefault(n,[]).append(rep)
        brute={tuple(x-y for x,y in zip(p,t))
               for group in buckets.values() for p in group for t in group}
        assert brute==set(short_vectors(q,h))
        for level in set(q):
            new=[]
            for c in brute:
                z=coordinates(q,c)
                if degree(c)<=level and any(zj and x>=level for x,zj in zip(q,z)):
                    new.append(c)
            expected={tuple(sign*x for x in v)
                      for radix,v in zip(q,carry_basis(q)) if radix==level
                      for sign in (-1,1)}
            assert set(new)==expected
        vector_ball_cases.append({'radices':q,'H':h,'vectors_including_zero':len(brute)})
    (DATA/'vector_ball_checks.json').write_text(json.dumps(vector_ball_cases,indent=2)+'\n')

    # Independent repeated-set addition, including the exact linearity boundary.
    small_profiles = [q for r in range(1,5)
                      for q in combinations_with_replacement(range(2,5),r)]
    count_sumset_checks = count_membership_checks = 0
    for q in small_profiles:
        a, d, sums = construct(q), sum(x-1 for x in q), {0}
        for h in range(d+4):
            if h:
                sums = {n+x for n in sums for x in a}
            assert len(sums) == sumset_size(q,h) == binomial_size(q,h)
            if h >= d-1:
                assert len(sums) == eventual_size(q,h)
            if d>=2 and h==d-2:
                assert len(sums) == eventual_size(q,h)+1
            for n in range(h*a[-1]+1):
                rep = canonical_representation(q,h,n)
                assert (rep is not None) == (n in sums)
                if rep is not None:
                    assert sum(rep)==h and sum(x*y for x,y in zip(rep,a))==n
                count_membership_checks += 1
            count_sumset_checks += 1

    # Explicit simultaneous/repeated-minimum, large-gap, and rank-zero examples.
    examples = []
    for q in [(), (2,), (3,3), (2,3,5), (2,2,4,7), (4,9), (2,11,11)]:
        a = construct(q)
        profile=[]
        bound = max(q,default=0)
        for h in range(bound+1):
            rel,_,_=relation_generators_at(a,h)
            rank = exact_rank(rel)
            assert rank == sum(x<=h for x in q)
            profile.append(rank)
        examples.append({'radices':q,'A':a,'basis':carry_basis(q),
                         'rank_profile':profile,'numerator':numerator(q),
                         'sumset_sizes':[sumset_size(q,h) for h in range(16)]})

    # Equal successive minima need not force equal later sumset sizes.
    same_minima=[]
    for a in [(0,1,3,9),(0,1,5,7)]:
        ranks=[]
        sizes=[]
        for h in range(9):
            rel,_,size=relation_generators_at(a,h)
            ranks.append(exact_rank(rel)); sizes.append(size)
        assert ranks[:4]==[0,0,0,2]
        same_minima.append({'A':a,'ranks':ranks,'sumset_sizes':sizes})
    assert same_minima[0]['sumset_sizes'] != same_minima[1]['sumset_sizes']

    # Input-validation regression test.
    q=(2,2)
    c=(-1,2,1,-2)  # intentionally not a relation: audit the validator rejects it
    try:
        coordinates(q,c)
    except ValueError:
        pass
    else:
        raise AssertionError('Invalid relation accepted')

    with (DATA/'rank_checks.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)
    (DATA/'examples.json').write_text(json.dumps(examples,indent=2)+'\n')
    (DATA/'equal_minima_different_sumsets.json').write_text(json.dumps(same_minima,indent=2)+'\n')
    result = {
        'status':'PASS','arithmetic':'exact Python integers; fraction-free Gaussian elimination',
        'python':sys.version.split()[0],
        'ordered_profiles_checked':len(profiles),
        'profile_domain':'r=1..4; 2<=h_1<=...<=h_r<=6',
        'degree_rank_checks':count_rank_checks,
        'weak_compositions_enumerated':count_multisets,
        'collision_generators_checked':count_generators,
        'arbitrarily_ordered_profiles_checked':len(unordered_profiles),
        'arbitrary_order_degree_rank_checks':unordered_rank_checks,
        'arbitrary_order_weak_compositions':unordered_multisets,
        'arbitrary_order_collision_generators':unordered_generators,
        'exhaustive_vector_ball_cases':len(vector_ball_cases),
        'exhaustive_vectors_including_zero':sum(x['vectors_including_zero'] for x in vector_ball_cases),
        'independent_set_addition_profiles':len(small_profiles),
        'independent_sumset_checks':count_sumset_checks,
        'individual_membership_checks':count_membership_checks,
        'additional_examples':len(examples),
        'limitations':'Finite checks are not a proof; the article gives the all-parameter proof.'}
    (DATA/'verification_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    print('Equal-minima examples:',json.dumps(same_minima))

if __name__=='__main__':
    main()
