#!/usr/bin/env python3
"""Exact finite checks for Lorentzian support enumerators.

Python 3.10+, standard library only. No floating point is used in identities,
coefficient inequalities, or covariance tests. These finite checks are not
proofs of the unrestricted theorems in article.tex.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod
from pathlib import Path
import json
import random
import sys
import time


def bits(mask: int):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def masks(n: int, k: int):
    for c in combinations(range(n), k):
        yield sum(1 << i for i in c)


def compositions_le(n: int, total: int):
    if n == 0:
        yield ()
        return
    for first in range(total + 1):
        for tail in compositions_le(n - 1, total - first):
            yield (first,) + tail


def demand_counts(rows: tuple[int, ...], n: int) -> list[int]:
    """Direct Hall-inequality enumeration, one count for each receiver support."""
    m = len(rows)
    neighbors = [sum(1 << x for x, row in enumerate(rows) if row & s)
                 for s in range(1 << n)]
    counts = [0] * (1 << n)
    for c in compositions_le(n, m):
        if all(sum(c[y] for y in bits(s)) <= neighbors[s].bit_count()
               for s in range(1, 1 << n)):
            counts[sum(1 << y for y in range(n) if c[y])] += 1
    return counts


def capacity_demand_counts(rows: tuple[int, ...], n: int,
                           capacities: tuple[int, ...]) -> list[int]:
    """Direct original capacity inequalities; does not expand cloned donors."""
    if len(rows) != len(capacities) or any(b < 0 for b in capacities):
        raise ValueError("One nonnegative capacity is required per donor.")
    bounds = [sum(b for row, b in zip(rows, capacities) if row & s)
              for s in range(1 << n)]
    counts = [0] * (1 << n)
    for c in compositions_le(n, sum(capacities)):
        if all(sum(c[y] for y in bits(s)) <= bounds[s]
               for s in range(1, 1 << n)):
            counts[sum(1 << y for y, value in enumerate(c) if value)] += 1
    return counts


def pair_data(rows: tuple[int, ...], n: int):
    """Independent recursive test for perfect matchability of two fixed shores."""
    m = len(rows)
    @lru_cache(None)
    def match(u: int, v: int) -> bool:
        if u.bit_count() != v.bit_count():
            return False
        if not u:
            return True
        x = next(bits(u))
        return any(match(u ^ (1 << x), v ^ (1 << y))
                   for y in bits(rows[x] & v))
    pairs = []
    by_support = [0] * (1 << n)
    for k in range(min(m, n) + 1):
        for v in masks(n, k):
            for u in masks(m, k):
                if match(u, v):
                    pairs.append((u, v))
                    by_support[v] += 1
    return by_support, pairs


def independent_ground(rows: tuple[int, ...], n: int, ground: tuple[int, ...]) -> bool:
    """Augmenting-path oracle for the private-copy transversal matroid.

    Elements 0..m-1 are private copies; m..m+n-1 are receivers.
    This routine does not call the fixed-shore matching recursion above.
    """
    m = len(rows)
    if len(ground) > m:
        return False
    owner = [-1] * m
    def augment(e: int, seen: set[int]) -> bool:
        adjacent = (e,) if e < m else tuple(x for x, r in enumerate(rows)
                                           if r & (1 << (e - m)))
        for x in adjacent:
            if x in seen:
                continue
            seen.add(x)
            if owner[x] < 0 or augment(owner[x], seen):
                owner[x] = e
                return True
        return False
    return all(augment(e, set()) for e in ground)


def basis_counts(rows: tuple[int, ...], n: int) -> list[int]:
    m = len(rows)
    out = [0] * (1 << n)
    for b in combinations(range(m + n), m):
        if independent_ground(rows, n, b):
            out[sum(1 << (e - m) for e in b if e >= m)] += 1
    return out


def size_counts(counts: list[int], n: int) -> list[int]:
    a = [0] * (n + 1)
    for s, count in enumerate(counts):
        a[s.bit_count()] += count
    return a


def ulc(a: list[int], r: int) -> None:
    if any(a[k] for k in range(r + 1, len(a))):
        raise AssertionError(('degree', a, r))
    a = (a + [0] * (r + 1))[:r + 1]
    for k in range(1, r):
        if a[k] ** 2 * k * (r - k) < a[k-1] * a[k+1] * (k+1) * (r-k+1):
            raise AssertionError(('ULC', a, r, k))
    occupied = [i for i, x in enumerate(a) if x]
    if occupied and occupied != list(range(occupied[0], occupied[-1] + 1)):
        raise AssertionError(('internal_zero', a))


def weighted_pair_counts(pairs, left_weights, right_weights) -> list[int]:
    out = [0] * (min(len(left_weights), len(right_weights)) + 1)
    for u, v in pairs:
        out[v.bit_count()] += prod(left_weights[x] for x in bits(u)) * \
                              prod(right_weights[y] for y in bits(v))
    return out


def determinant(a: list[list[Fraction]]) -> Fraction:
    a = [row[:] for row in a]
    ans = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            ans = -ans
        p = a[j][j]
        ans *= p
        for i in range(j+1, len(a)):
            factor = a[i][j] / p
            for k in range(j+1, len(a)):
                a[i][k] -= factor * a[j][k]
    return ans


def covariance_check(counts: list[int], n: int, m: int, weights: list[int]):
    if m == 0:
        return
    masses = [count * prod(weights[y] for y in bits(s))
              for s, count in enumerate(counts)]
    total = sum(masses)
    p = [Fraction(sum(w for s, w in enumerate(masses) if s >> i & 1), total)
         for i in range(n)]
    cov = [[Fraction(sum(w for s, w in enumerate(masses)
                        if s >> i & 1 and s >> j & 1), total) - p[i]*p[j]
            for j in range(n)] for i in range(n)]
    bound_minus_cov = [[(p[i] if i == j else 0) - p[i]*p[j]/m - cov[i][j]
                        for j in range(n)] for i in range(n)]
    for s in range(1, 1 << n):
        ids = list(bits(s))
        minor = [[bound_minus_cov[i][j] for j in ids] for i in ids]
        if determinant(minor) < 0:
            raise AssertionError(('covariance', counts, weights, s))


def relation_is_transitive(rows: tuple[int, ...]) -> bool:
    return all(rows[j] & ~row == 0 for row in rows for j in bits(row))


def preorder_counts(rows: tuple[int, ...]) -> list[int]:
    """Original ideal inequalities, not neighborhood/Hall inequalities."""
    n = len(rows)
    ideals = [s for s in range(1 << n)
              if all(not (row & s) or s >> x & 1 for x, row in enumerate(rows))]
    out = [0] * (1 << n)
    for c in compositions_le(n, n):
        if all(sum(c[x] for x in bits(s)) <= s.bit_count() for s in ideals):
            out[sum(1 << x for x, v in enumerate(c) if v)] += 1
    return out


def gamma_from_h(h: list[int]) -> list[int]:
    n = len(h)-1
    rem = h[:]
    gamma = []
    for k in range(n//2+1):
        v = rem[k]
        gamma.append(v)
        for j in range(n-2*k+1):
            rem[k+j] -= v*comb(n-2*k,j)
    if any(rem):
        raise AssertionError(('nonsymmetric_gamma', h))
    return gamma


def conditional_checks(counts: list[int], m: int, n: int) -> int:
    checks = 0
    for choices in product(range(3), repeat=n):
        present = sum(1 << i for i, v in enumerate(choices) if v == 1)
        absent = sum(1 << i for i, v in enumerate(choices) if v == 2)
        a = [0]*(n+1)
        for s, c in enumerate(counts):
            if s & present == present and not s & absent:
                a[(s ^ present).bit_count()] += c
        if any(a):
            ulc(a, m-present.bit_count())
            checks += 1
    return checks


def check_graph(rows, n, extra=False):
    direct = demand_counts(rows, n)
    pairsupport, pairs = pair_data(rows, n)
    basis = basis_counts(rows, n)
    if not (direct == pairsupport == basis):
        raise AssertionError(('bridge_or_lift', rows, n, direct, pairsupport, basis))
    a = size_counts(direct, n)
    ulc(a, min(len(rows), n))
    weights_x = [1+x%3 for x in range(len(rows))]
    weights_y = [2+y%3 for y in range(n)]
    ulc(weighted_pair_counts(pairs, weights_x, weights_y), min(len(rows), n))
    if extra:
        covariance_check(direct, n, len(rows), weights_y)
    return direct, conditional_checks(direct, len(rows), n) if extra else 0


def run(max_preorder: int, include_3x4: bool):
    started = time.monotonic()
    out = {'python':sys.version.split()[0], 'seed':20260929,
           'finite_checks_only':True, 'bipartite':[], 'preorders':[]}
    cond = 0
    total_graphs = 0
    for m in range(4):
        for n in range(4):
            for encoding in range(1 << (m*n)):
                rows = tuple((encoding >> (n*x)) & ((1 << n)-1) for x in range(m))
                _, c = check_graph(rows, n, extra=True)
                cond += c
            count = 1 << (m*n)
            total_graphs += count
            out['bipartite'].append({'m':m,'n':n,'graphs':count})
    if include_3x4:
        for encoding in range(1 << 12):
            rows = tuple((encoding >> (4*x)) & 15 for x in range(3))
            check_graph(rows, 4)
        total_graphs += 4096
        out['bipartite'].append({'m':3,'n':4,'graphs':4096})
    out['total_bipartite_graphs'] = total_graphs
    out['nonempty_conditioning_events'] = cond
    out['covariance_graphs'] = sum(1 << (m*n) for m in range(1,4) for n in range(4))
    for n in range(max_preorder+1):
        off = [(i,j) for i in range(n) for j in range(n) if i != j]
        count = 0
        for encoding in range(1 << len(off)):
            rows = [1 << i for i in range(n)]
            for b, (i,j) in enumerate(off):
                if encoding >> b & 1:
                    rows[i] |= 1 << j
            rows = tuple(rows)
            if not relation_is_transitive(rows):
                continue
            count += 1
            actual = preorder_counts(rows)
            predicted, _ = pair_data(rows, n)
            if actual != predicted:
                raise AssertionError(('preorder', rows, actual, predicted))
            h = size_counts(actual, n)
            ulc(h,n)
            if h != h[::-1]:
                raise AssertionError(('palindromicity', rows,h))
        out['preorders'].append({'n':n,'count':count})
        print(f'preorders n={n}: {count} passed',flush=True)
    rng = random.Random(20260929)
    random_graphs=[]
    for m,n in [(4,4),(5,4),(4,5)]:
        for _ in range(25):
            rows = tuple(rng.randrange(1 << n) for x in range(m))
            check_graph(rows,n,extra=False)
            random_graphs.append({'m':m,'n':n,'rows':rows})
    out['seeded_graphs'] = random_graphs
    # Theta_3: left=(a,c1,c2,c3), right=(b,d1,d2,d3), paths a-di-ci-b.
    theta = (14,3,5,9)
    counts,_ = pair_data(theta,4)
    p = size_counts(counts,4)
    if p != [1,9,24,16,1]:
        raise AssertionError(('theta',p))
    h = [0]*9
    for k, coeff in enumerate(p):
        for j in range(8-2*k+1):
            h[k+j] += coeff*comb(8-2*k,j)
    ulc(p,4)
    ulc(h,8)
    # Eight-element height-two preorder; independent direct ideal count.
    rel = tuple((1 << i) | (theta[i] << 4) for i in range(4)) + \
          tuple(1 << i for i in range(4,8))
    if size_counts(preorder_counts(rel),8) != h:
        raise AssertionError('theta ideal count')
    out['theta3'] = {'rows':theta,'p':p,'h':h,'lattice_points':sum(h),
                     'normalized_p':[str(Fraction(v,comb(4,k))) for k,v in enumerate(p)]}
    # Integer-capacity extension, checked against direct capacity inequalities.
    capacities = []
    for encoding in range(16):
        rows = tuple((encoding >> (2*x)) & 3 for x in range(2))
        for b in [(2,1),(1,2),(2,2),(3,1)]:
            cloned = tuple(row for row,bx in zip(rows,b) for _ in range(bx))
            c,_ = check_graph(cloned,2)
            direct = capacity_demand_counts(rows, 2, b)
            if c != direct:
                raise AssertionError(("capacity", rows, b, c, direct))
            capacities.append({'rows':rows,'capacities':b,'counts':c})
    out['capacity_cases'] = len(capacities)
    out['capacity_data'] = capacities
    out['all_checks_passed'] = True
    out['elapsed_seconds'] = round(time.monotonic()-started,3)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-preorder', type=int, default=4, choices=range(6))
    parser.add_argument('--skip-3x4', action='store_true')
    parser.add_argument('--output', type=Path, default=Path('results/verification.json'))
    args = parser.parse_args()
    results = run(args.max_preorder,not args.skip_3x4)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in results.items()
                      if k not in ['seeded_graphs','capacity_data']},indent=2))

if __name__ == '__main__':
    main()
