#!/usr/bin/env python3
"""Reproducible finite audits, independent enumerations, and CRT reduction tests."""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb,gcd,lcm
from pathlib import Path
import json, random, sys
from crossover_masks import (Ray,analyze,support,crt_pair,compatibility_graph,
                            maximum_clique,graph_to_endpoint_rays,marker_family)

COUNTS: Counter[str] = Counter()

def check(group: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f'failed in {group} after {COUNTS[group]} checks')
    COUNTS[group] += 1


def literal_crossover(words: set[int], n: int) -> set[int]:
    answer: set[int] = set()
    full = (1 << n)-1
    for cut in range(n+1):
        left = (1 << cut)-1
        right = full ^ left
        prefixes = {w & left for w in words}
        suffixes = {w & right for w in words}
        answer.update(x|y for x in prefixes for y in suffixes)
    return answer


def all_subsets(positions: set[int], max_ones: int) -> set[int]:
    return {sum(1 << i for i in chosen)
            for r in range(min(max_ones,len(positions))+1)
            for chosen in combinations(sorted(positions),r)}


def audit_generations() -> None:
    for k in range(1,9):
        rays = marker_family(k)
        for t in range(3):
            n = (k+1)*t+k
            positions = support(rays,n)
            check('family_supports',positions == {j*(t+1)-1 for j in range(1,k+1)})
            generation = {0} | {1 << i for i in positions}
            for g in range(5):
                expected = all_subsets(positions,2**g)
                check('literal_generation_sets',generation == expected)
                check('generation_counts',len(generation) == sum(comb(k,r) for r in range(min(k,2**g)+1)))
                generation = literal_crossover(generation,n)
        result = analyze(rays)
        check('family_depth',result['maximum_sites'] == k)
        check('family_depth',result['parallel_stabilization_depth'] == (k-1).bit_length())
        check('family_class',result['class'] == ('linear context-free, nonregular' if k==1 else 'not context-free'))
    # The four-word non-CFL slice, including its zero-length-block edge case.
    for t in range(31):
        n = 3*t+2
        rays = marker_family(2)
        words = {0}|{1 << i for i in support(rays,n)}
        check('depth_one_example',len(words)==3)
        out = literal_crossover(words,n)
        check('depth_one_example',len(out)==4)
        check('depth_one_example',out==all_subsets(support(rays,n),2))


def eventual_bound(rays: list[Ray]) -> int:
    inf = [r for r in rays if r.q]
    period = lcm(*(r.q for r in inf)) if inf else 1
    bound = max((r.n0 for r in rays),default=0)+1
    for r,s in combinations(inf,2):
        a,b = r.affine(); c,d = s.affine()
        if a != c:
            crossing=(d-b)/(a-c)
            bound=max(bound,crossing.numerator//crossing.denominator+1)
    return max(0,bound)+period


def audit_random_rays() -> None:
    rng=random.Random(20260930)
    for _ in range(600):
        rays=[Ray((rng.randrange(5),rng.randrange(5)),
                  (rng.randrange(4),rng.randrange(4))) for _ in range(rng.randrange(1,7))]
        res=analyze(rays)
        stop=eventual_bound(rays)
        observed=max(len(support(rays,n)) for n in range(stop+1))
        check('clique_vs_complete_period',observed==res['maximum_sites'])
        # A separate phase/velocity test on the full common period.
        inf=[r for r in rays if r.q]
        period=lcm(*(r.q for r in inf)) if inf else 1
        interior_any=False; two=False
        for phase in range(period):
            velocities={r.affine()[0] for r in inf if (phase-r.n0)%r.q==0 and all(r.step)}
            interior_any |= bool(velocities)
            two |= len(velocities)>=2
        cls='not context-free' if two else ('linear context-free, nonregular' if interior_any else 'regular')
        check('pair_vs_all_phases',cls==res['class'])
        # Independent literal closure at a small chosen length.
        n=rng.randrange(1,12)
        positions=support(rays,n)
        gen={0}|{1 << i for i in positions}
        for g in range(3):
            check('random_literal_generations',gen==all_subsets(positions,2**g))
            gen=literal_crossover(gen,n)


def audit_graph_reduction() -> None:
    for n in range(1,6):
        pairs=list(combinations(range(n),2))
        for mask in range(1 << len(pairs)):
            graph=[set() for _ in range(n)]
            for bit,(v,w) in enumerate(pairs):
                if mask >> bit & 1:
                    graph[v].add(w);graph[w].add(v)
            rays=graph_to_endpoint_rays(graph)
            _,image=compatibility_graph(rays)
            check('all_graphs_through_five',image==graph)
            check('clique_preservation',analyze(rays)['maximum_sites']==len(maximum_clique(graph)))
            check('regular_hardness_instances',analyze(rays)['class']=='regular')
    rng=random.Random(61030)
    for _ in range(100):
        n=rng.randrange(6,11);graph=[set() for _ in range(n)]
        for v,w in combinations(range(n),2):
            if rng.randrange(2):graph[v].add(w);graph[w].add(v)
        rays=graph_to_endpoint_rays(graph)
        check('larger_graph_reductions',compatibility_graph(rays)[1]==graph)


def audit_edges_and_crt() -> None:
    check('edge_cases',analyze([])['maximum_sites']==0)
    check('edge_cases',analyze([])['parallel_stabilization_depth']==0)
    check('edge_cases',analyze([Ray((0,0),(0,0))])['class']=='regular')
    # Different interior speeds, but incompatible parity: linear, not non-CFL.
    separated=[Ray((0,0),(1,3)),Ray((0,1),(3,1))]
    check('edge_cases',analyze(separated)['class']=='linear context-free, nonregular')
    # Infinite duplicates must count once; a finite point can raise the maximum.
    dup=[Ray((0,0),(1,1)),Ray((1,1),(1,1)),Ray((0,2),(0,0))]
    check('edge_cases',analyze(dup)['maximum_sites']==2)
    for m in range(1,13):
        for n in range(1,13):
            for a in range(m):
                for b in range(n):
                    out=crt_pair(a,m,b,n)
                    brute=[x for x in range(lcm(m,n)) if x%m==a and x%n==b]
                    check('crt_exhaustive', (out is None and not brute) or (bool(brute) and out==(brute[0],lcm(m,n))))


def main() -> None:
    audit_edges_and_crt();audit_generations();audit_random_rays();audit_graph_reduction()
    report={'status':'PASS','python':sys.version.split()[0],
            'random_seeds':[20260930,61030], 'checks_by_group':dict(COUNTS),
            'total_checks':sum(COUNTS.values()),
            'scope':'Exact finite tests; not formal proofs or a general Presburger implementation.'}
    out=Path(__file__).resolve().parent.parent/'data'/'verification.json'
    out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
