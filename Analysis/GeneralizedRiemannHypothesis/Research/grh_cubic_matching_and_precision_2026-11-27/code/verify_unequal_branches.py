#!/usr/bin/env python3
"""Exact checks for unequal-precision branch-jet recovery.

All arithmetic is finite-field arithmetic in Python's integers.  The linear
algebra checker expands H(X,u_b(X)) directly, independently of the Newton
kernel formula.  The tree dynamic program is independently compared with
exhaustive deletion of branch subsets.  No floating-point arithmetic is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import json
import random
import argparse


def add(a, b, p, size):
    out = [0] * size
    for i in range(size):
        out[i] = ((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p
    return out


def mul(a, b, p, size):
    out = [0] * size
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if i + j < size:
                    out[i+j] = (out[i+j] + x*y) % p
    return out


def rank_mod(matrix, p):
    if not matrix:
        return 0
    a = [row[:] for row in matrix]
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c] % p), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][c] % p, -1, p)
        a[r] = [(x*inv) % p for x in a[r]]
        for i in range(r + 1, len(a)):
            fac = a[i][c] % p
            if fac:
                a[i] = [(x-fac*y) % p for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def contact_matrix(branches, p):
    n = len(branches)
    s = [[0]*n for _ in range(n)]
    for i in range(n):
        assert branches[i][0] % p == 0
        for j in range(i):
            length = max(len(branches[i]), len(branches[j]))
            k = next((k for k in range(length)
                      if ((branches[i][k] if k < len(branches[i]) else 0)
                          - (branches[j][k] if k < len(branches[j]) else 0)) % p), None)
            if k is None:
                raise ValueError('Branches must be pairwise distinct')
            assert k >= 1
            s[i][j] = s[j][i] = k
    return s


def greedy(s, precision, subset=None):
    unused = set(range(len(s)) if subset is None else subset)
    order, scores = [], []
    while unused:
        b = max(unused, key=lambda b: (precision[b]-sum(s[b][c] for c in order), -b))
        scores.append(precision[b]-sum(s[b][c] for c in order))
        order.append(b)
        unused.remove(b)
    return order, scores


def observations(branches, precision, p, d):
    """Direct matrix with domain monomials of total degree < cutoff."""
    cutoff = max(d, max(precision, default=0))
    monomials = [(a, b) for a in range(cutoff) for b in range(cutoff-a)]
    rows = []
    for branch, n in zip(branches, precision):
        powers = [[1] + [0]*(cutoff-1)]
        for b in range(1, cutoff):
            powers.append(mul(powers[-1], branch, p, cutoff))
        for k in range(n):
            rows.append([powers[b][k-a] if k >= a else 0 for a,b in monomials])
    target = [[int(j == i) for j in range(len(monomials))]
              for i, (a,b) in enumerate(monomials) if a+b < d]
    return rows, target, monomials


def unresolved_by_matrix(branches, precision, p, d):
    matrix, target, _ = observations(branches, precision, p, d)
    return rank_mod(matrix + target, p) - rank_mod(matrix, p)


def unresolved_by_formula(s, precision, d):
    _, score = greedy(s, precision)
    return sum(max(0, d-j-max(0, score[j])) for j in range(d))


@dataclass(frozen=True)
class Node:
    leaves: tuple[int, ...]
    stem: int
    children: tuple['Node', ...] = ()


def make_tree(s, leaves=None, parent_level=0):
    leaves = tuple(range(len(s)) if leaves is None else leaves)
    if len(leaves) == 1:
        return Node(leaves, 0)
    level = min(s[a][b] for a,b in combinations(leaves, 2))
    remain = set(leaves)
    parts = []
    while remain:
        a = min(remain)
        part = tuple(sorted(b for b in remain if b == a or s[a][b] > level))
        parts.append(part)
        remain.difference_update(part)
    assert len(parts) >= 2
    return Node(leaves, level-parent_level,
                tuple(make_tree(s, part, level) for part in parts))


def tree_scores(node, precision):
    if not node.children:
        return [precision[node.leaves[0]]]
    merged = sorted((x for c in node.children for x in tree_scores(c, precision)), reverse=True)
    return [value-j*node.stem for j, value in enumerate(merged)]


def capacity_function(tree, precision):
    @lru_cache(None)
    def cap(node, j, threshold):
        if j >= len(node.leaves) or threshold >= max(precision[b] for b in node.leaves):
            return len(node.leaves)
        if not node.children:
            return int(precision[node.leaves[0]] <= threshold)
        child_threshold = threshold + j*node.stem
        values = [0] + [-10**9]*j
        for child in node.children:
            nxt = [-10**9]*(j+1)
            for used in range(j+1):
                for allocated in range(j-used+1):
                    nxt[used+allocated] = max(nxt[used+allocated],
                                             values[used]+cap(child, allocated, child_threshold))
            values = nxt
        return max(values)
    return cap



def capacity_table(tree, precision, max_rank):
    """All C_v(j,T), batched in the shifted child threshold U.

    This implementation has O(N*d^2*(n_max+1)) integer operations, where
    d=max_rank+1 and the compact tree has O(N) nodes.
    """
    nmax = max(precision, default=0)
    d = max_rank + 1
    def build(node):
        if not node.children:
            b = node.leaves[0]
            return [[int(j >= 1 or precision[b] <= t) for t in range(nmax+1)]
                    for j in range(d)]
        children = [build(c) for c in node.children]
        merged = [[0]*(nmax+1) for _ in range(d)]
        for u in range(nmax+1):
            vals = [0] + [-10**9]*(d-1)
            for child in children:
                nxt = [-10**9]*d
                for used in range(d):
                    for allocated in range(d-used):
                        nxt[used+allocated] = max(nxt[used+allocated],
                                                vals[used]+child[allocated][u])
                vals = nxt
            best = -10**9
            for j in range(d):
                best = max(best, vals[j])
                merged[j][u] = best
        return [[merged[j][min(nmax, t+j*node.stem)] for t in range(nmax+1)]
                for j in range(d)]
    return build(tree)


def capacity_exhaustive(s, precision, j, threshold=0):
    n = len(s)
    best = ()
    for size in range(n+1):
        for subset in combinations(range(n), size):
            _, scores = greedy(s, precision, subset)
            ok = j >= size or scores[j] <= threshold
            if ok and size > len(best):
                best = subset
    return len(best), best


def multiplicative_branch(b, p):
    # Exact binomial coefficients reduced modulo p.
    from math import comb
    return [0] + [comb(b,k) % p for k in range(1,b+1)]


def check_case(branches, precision, p, counters, check_linear=True, check_deletions=True):
    s = contact_matrix(branches, p)
    tree = make_tree(s)
    order, scores = greedy(s, precision)
    assert scores == tree_scores(tree, precision)
    counters['tree_merge_profiles'] += 1
    assert all(scores[j+1] <= scores[j]-1 for j in range(len(scores)-1))
    if check_linear:
        for d in range(1, len(branches)+1):
            a = unresolved_by_matrix(branches, precision, p, d)
            b = unresolved_by_formula(s, precision, d)
            assert a == b, (p, branches, precision, d, a, b)
            counters['direct_linear_jet_checks'] += 1
            if scores[d-1] > 0:
                # Extract the d selected branches as a clean certificate.
                chosen = order[:d]
                assert all(precision[b] > sum(s[b][c] for c in chosen if c != b)
                           for b in chosen)
                counters['sparse_certificates'] += 1
    if check_deletions:
        cap = capacity_function(tree, tuple(precision))
        table = capacity_table(tree, precision, len(branches)-1)
        for j in range(len(branches)):
            expected, _ = capacity_exhaustive(s, precision, j)
            got = cap(tree, j, 0)
            assert got == expected == table[j][0], (precision, j, got, expected)
            counters['pruning_vs_all_subsets'] += 1
        # Independently check the saturation thresholds in the theorem.
        for d in range(1, len(branches)+1):
            distance = len(branches)-cap(tree, d-1, 0)
            saturated = all(precision[b] >= 1+sum(sorted(s[b], reverse=True)[:d-1])
                            for b in range(len(branches)))
            assert (distance == len(branches)-d+1) == saturated
            counters['anisotropic_saturation_checks'] += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]/'results'/'unequal_branches.json')
    args = parser.parse_args()
    counters = {k:0 for k in ['tree_merge_profiles','direct_linear_jet_checks',
                'sparse_certificates','pruning_vs_all_subsets','anisotropic_saturation_checks']}
    binary = [multiplicative_branch(b, 2) for b in range(4)]
    for precision in product(range(5), repeat=4):
        check_case(binary, precision, 2, counters)
    rng = random.Random(20261127)
    for p in (2,3,5):
        for _ in range(40):
            count = rng.randint(2,6)
            available = list(product(range(p), repeat=5))
            chosen = rng.sample(available, count)
            branches = [[0] + list(a) for a in chosen]
            precision = [rng.randrange(10) for _ in branches]
            check_case(branches, precision, p, counters)
    # Named mixed-precision binary example.
    branches = [multiplicative_branch(b,2) for b in range(8)]
    precision = [6,4,9,5,8,3,7,4]
    s = contact_matrix(branches,2)
    order, scores = greedy(s,precision)
    distance_table = {}
    for d in range(1,9):
        c, subset = capacity_exhaustive(s,precision,d-1)
        distance_table[str(d)] = {'distance':8-c,'maximal_zero_set':list(subset)}
    example = {'field':2,'directions':list(range(8)),'precisions':precision,
               'order':order,'scores':scores,'total_recorded_coefficients':sum(precision),
               'distances':distance_table,
               'jet_3_witness':'Y*(Y+X+X^2+X^3)',
               'jet_3_witness_nonzero_blocks':[1,2,4,6]}
    check_case(branches,precision,2,counters)
    witness_values = [mul(u, add(u, branches[3], 2, 9), 2, 9) for u in branches]
    support = [b for b,v in enumerate(witness_values) if any(v[:precision[b]])]
    assert support == [1,2,4,6]
    # Five irregular branches, sharp one-corruption budget.
    branches2 = [[0],[0,0,0,0,0,1],[0,1],[0,2],[0,3]]
    precision2 = [7,7,3,3,3]
    s2 = contact_matrix(branches2,5)
    c2, witness2 = capacity_exhaustive(s2,precision2,2)
    assert 5-c2 == 3
    check_case(branches2,precision2,5,counters)
    budget_example = {'field':5,'branches':['0','X^5','X','2X','3X'],
                      'jet_order':3,'precisions':precision2,
                      'distance':3,'correctable_arbitrary_blocks':1,
                      'minimum_total_precision_for_distance_3':sum(precision2),
                      'minimum_uniform_precision':7,
                      'uniform_total_precision':35}
    result = {'status':'PASS','arithmetic':'exact finite fields; no floating point',
              'seed':20261127,'checks':counters,'binary_example':example,
              'budget_example':budget_example,
              'scope':'Finite checks support, but do not replace, the general proof.'}
    destination=args.output
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
