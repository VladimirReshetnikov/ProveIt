"""Reproduce the finite checks and exact symbolic certificates.
Run from this directory: python verify.py
Finite tests supplement, and do not replace, the article's proofs.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb
from pathlib import Path
from random import Random
import json
import platform
import time
from support_kernels import (bipartite_counts, bipartite_population_counts,
    relation_counts, sample_relation_support, rank_three_counts,
    rank_four_family_counts, rank_ulc_gaps, trim, quota_vectors)
from certificates import verify_certificates


def brute_bipartite(rows, m):
    """Independent incremental generation of supports via matching extensions."""
    states = {(0, 0)}
    for i, row in enumerate(rows):
        additions = set()
        for lm, rm in states:
            available = row & ~rm
            while available:
                bit = available & -available
                available -= bit
                additions.add((lm | 1 << i, rm | bit))
        states |= additions
    counts = Counter(lm.bit_count() for lm, rm in states)
    return [counts[i] for i in range(max(counts)+1)]


def brute_relation(n, arcs, weighted=False):
    edges = set(arcs)
    out = [0]*(n//2+1)
    for status in product(range(3), repeat=n):
        a = tuple(i for i in range(n) if status[i] == 1)
        b = tuple(i for i in range(n) if status[i] == 2)
        if len(a) != len(b):
            continue
        if not any(all((u, v) in edges for u, v in zip(a, perm))
                   for perm in permutations(b)):
            continue
        weight = 1
        if weighted:
            for u in a:
                weight *= u+1
            for v in b:
                weight *= 2*v+1
        out[len(a)] += weight
    return trim(out)


def equality_shape(n, arcs):
    """Stars/triangles with equal directed-arc counts in nontrivial components."""
    edges = {(u, v) for u, v in arcs if u != v}
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    seen, sizes = set(), []
    for root in range(n):
        if root in seen or not adj[root]:
            continue
        component, pending = set(), [root]
        while pending:
            u = pending.pop()
            if u not in component:
                component.add(u); pending.extend(adj[u]-component)
        seen |= component
        undirected = {tuple(sorted((u, v))) for u in component for v in adj[u]}
        star = any(all(u in e for e in undirected) for u in component)
        triangle = len(component) == 3 and len(undirected) == 3
        if not (star or triangle):
            return False
        sizes.append(sum(u in component for u, v in edges))
    return len(set(sizes)) <= 1


def det3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def main():
    start = time.perf_counter()
    report = {'python': platform.python_version(),
              'arithmetic': 'integer and Fraction; no floating-point assertions',
              'repository_commit': 'ffddaa8b9c89e7bf027e1442cc6216bb010906d0'}
    nb = 0
    for mask in range(1 << 12):
        rows = [(mask >> (4*i)) & 15 for i in range(3)]
        p = brute_bipartite(rows, 4)
        assert p == bipartite_counts(rows, 4)
        assert all(g >= 0 for g in rank_ulc_gaps(p))
        nb += 1
    report['all_bipartite_3_by_4_graphs'] = nb
    rank_histogram = Counter()
    mixed_rank_three = 0
    for mask in range(1 << 16):
        rows = [(mask >> (4*i)) & 15 for i in range(4)]
        p = brute_bipartite(rows, 4)
        rank = len(p)-1
        rank_histogram[rank] += 1
        assert all(g >= 0 for g in rank_ulc_gaps(p))
        if rank == 3 and all(rows) and (rows[0] | rows[1] | rows[2] | rows[3]) == 15:
            mixed_rank_three += 1
    report['all_bipartite_4_by_4_graphs_reference_only'] = {
        'graphs': 65536, 'rank_histogram': dict(sorted(rank_histogram.items())),
        'rank_three_without_isolates': mixed_rank_three,
        'note': 'Rank-four checks are finite evidence only.'}
    nr = np = 0
    lattice_candidates = lattice_points = 0
    available = [(u, v) for u in range(4) for v in range(4) if u != v]
    for mask in range(1 << 12):
        arcs = {e for i, e in enumerate(available) if mask >> i & 1}
        p = brute_relation(4, arcs)
        assert p == relation_counts(4, arcs)
        d = len(p)-1
        if d >= 2:
            gap = (d-1)*p[1]**2-2*d*p[2]
            assert gap >= 0
            assert (gap == 0) == equality_shape(4, arcs)
        reflexive = arcs | {(i, i) for i in range(4)}
        is_preorder = all((a, c) in reflexive for a, b in reflexive
                          for bb, c in reflexive if bb == b)
        np += int(is_preorder)
        if is_preorder:
            ideals = [S for S in range(16) if all(
                not (S >> v & 1) or (S >> u & 1) for u, v in reflexive)]
            h = [0]*5
            for xx in quota_vectors([4]*4, 4):
                lattice_candidates += 1
                if all(sum(xx[v] for v in range(4) if S >> v & 1)
                       <= S.bit_count() for S in ideals):
                    h[sum(t > 0 for t in xx)] += 1
                    lattice_points += 1
            reconstructed = [sum(p[k]*comb(4-2*k, j-k)
                for k in range(len(p)) if 0 <= j-k <= 4-2*k)
                for j in range(5)]
            assert h == reconstructed
        if mask % 17 == 0:
            w = brute_relation(4, arcs, True)
            if d >= 2:
                assert (d-1)*w[1]**2 >= 2*d*w[2]
        nr += 1
    report['all_loopless_directed_relations_on_4_vertices'] = nr
    report['preorders_among_these_after_adding_loops'] = np
    count = 0
    for x, y, z, w in product(range(6), repeat=4):
        for alpha, beta in product(range(2), repeat=2):
            p = rank_three_counts(x, y, z, w, alpha, beta)
            assert p == bipartite_population_counts(1, 2, alpha+2*beta,
                                                     [x, y, z], [w])
            assert all(g >= 0 for g in rank_ulc_gaps(p))
            count += 1
    report['rank_three_population_specializations'] = count
    report['direct_preorder_polytope_checks'] = {'preorders': np,
        'candidate_vectors': lattice_candidates, 'feasible_points_total': lattice_points}
    family_samples = {}
    for N in [1, 2, 3, 5, 10, 100, 10**6]:
        p = rank_four_family_counts(N)
        assert p == bipartite_population_counts(2, 2, 15, [N]*3, [N]*3)
        assert all(g > 0 for g in rank_ulc_gaps(p))
        family_samples[str(N)] = p
    report['rank_four_family_samples'] = family_samples
    report['symbolic_certificates'] = verify_certificates()
    matrix = [[1+i*j+i*i*j*j for j in range(1, 10)] for i in range(1, 10)]
    for rr in combinations(range(9), 2):
        for cc in combinations(range(9), 2):
            assert matrix[rr[0]][cc[0]]*matrix[rr[1]][cc[1]] > (
                   matrix[rr[0]][cc[1]]*matrix[rr[1]][cc[0]])
    for rr in combinations(range(9), 3):
        for cc in combinations(range(9), 3):
            assert det3([[matrix[i][j] for j in cc] for i in rr]) > 0
    minors = [comb(9, k)**2 for k in range(4)]
    gap = minors[2]**2-3*minors[1]*minors[3]
    assert gap == -34992
    report['bimatroid_counterexample'] = {'minor_counts': minors,
       'rank_three_second_gap': gap, 'positive_2_minors': comb(9, 2)**2,
       'positive_3_minors': comb(9, 3)**2}
    rng = Random(20260930)
    arcs = {(0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (1, 5)}
    for k in (None, 0, 1, 2):
        for _ in range(100):
            a, b = sample_relation_support(6, arcs, rng, k)
            assert set(a).isdisjoint(b) and len(a) == len(b)
            assert k is None or len(a) == k
            assert any(all((u, v) in arcs for u, v in zip(a, p))
                       for p in permutations(b))
    report['exact_sampler_validity_checks'] = 400
    report['elapsed_seconds_informational_only'] = round(time.perf_counter()-start, 3)
    report['status'] = 'All assertions passed.'
    out = Path(__file__).resolve().parents[1]/'data'/'verification.json'
    out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
