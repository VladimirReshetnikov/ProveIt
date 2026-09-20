#!/usr/bin/env python3
"""Exact, dependency-free checks for the numerical-semigroup leaf article.

Run: python code/verify.py --out data
All arithmetic in the certificate checks is integer arithmetic.  This verifies
finite instances; the infinite-family and asymptotic proofs are in article.tex.
"""
from __future__ import annotations
import argparse
import csv
import heapq
import json
import platform
import sys
import time
from pathlib import Path
from typing import Iterable


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def conjectured_bound(g: int) -> int:
    q, r = divmod(g, 4)
    return 2 * q + (-1 if r in (0, 1) else r - 2)


def is_basis(D: set[int], d: int) -> bool:
    return D <= set(range(d + 1)) and {0, d} <= D and {
        a + b for a in D for b in D
    } == set(range(2 * d + 1))


def construction(D: Iterable[int], d: int, delta: int = 0) -> tuple[list[int], int]:
    D = set(D)
    require(d >= 1 and delta >= 0 and is_basis(D, d), 'Invalid basis or parameters')
    M = 4 * d + 1 + delta
    m = M + 1
    B = D | set(range(2 * d + 1, M))
    return sorted(m + b for b in B), 2 * m


def inspect_tail(A: Iterable[int], c: int) -> dict:
    """Check S={0} union A union [c,infinity), without using family formulas."""
    A = sorted(set(A))
    require(A and 0 < A[0] and A[-1] < c, 'Invalid tail description')
    m = A[0]
    F = c - 1
    require(F not in A, 'The specified conductor is not the exact conductor')
    ng = sum(1 << a for a in A)
    G = ((1 << c) - 2) ^ ng
    require(all(((ng << a) & G) == 0 for a in A), 'Closure fails below conductor')
    sums = 0
    for a in A:
        sums |= ng << a
    # Above F+m every s decomposes as m+(s-m), with s-m >= c.
    tail_primitive = [n for n in range(c, c + m) if not (sums >> n) & 1]
    left_primitive = [a for a in A if not (sums >> a) & 1]
    gaps = [n for n in range(1, c) if (G >> n) & 1]
    pf = [p for p in gaps if ((ng << p) & G) == 0]
    gens = left_primitive + tail_primitive
    g, t = len(gaps), len(pf)
    leaf = not tail_primitive
    if leaf:
        h = 2 * g - 3 * t
        require(t <= m - 2, 'Leaf multiplicity/type bound fails')
        require(F >= 2 * m - 1, 'Leaf conductor bound fails')
        require(3 * t + 3 <= 2 * g, 'Linear upper bound fails')
        require(h * h >= 4 * t - 3, 'Quadratic upper bound fails')
    return dict(m=m, F=F, c=c, g=g, t=t, leaf=leaf,
                conjectured_bound=conjectured_bound(g),
                violation=t-conjectured_bound(g), generators=gens,
                nongaps_below_conductor=A, gaps=gaps, pseudo_frobenius=pf)


def from_generators(gens: Iterable[int]) -> dict:
    """Independent reconstruction using Dijkstra on residues modulo m."""
    gens = sorted(set(gens))
    m = gens[0]
    w: list[int | None] = [None] * m
    w[0] = 0
    heap = [(0, 0)]
    while heap:
        value, residue = heapq.heappop(heap)
        if w[residue] != value:
            continue
        for a in gens:
            r, candidate = (residue + a) % m, value + a
            if w[r] is None or candidate < w[r]:
                w[r] = candidate
                heapq.heappush(heap, (candidate, r))
    require(all(x is not None for x in w), 'Generators do not have gcd 1')
    ap = [int(x) for x in w]
    def contains(n: int) -> bool:
        return n >= 0 and n >= ap[n % m]
    F = max(ap) - m
    g = sum((ap[i] - i) // m for i in range(m))
    maximal = [a for a in ap if not any(b != a and contains(b-a) for b in ap)]
    pf = sorted(a-m for a in maximal)
    actual_gens = [n for n in range(1, F+m+1) if contains(n) and not any(
        contains(a) and contains(n-a) for a in range(m, n//2+1))]
    return dict(m=m, F=F, g=g, t=len(pf), apery=ap,
                pseudo_frobenius=pf, generators=actual_gens,
                leaf=all(a <= F for a in actual_gens))


def family_record(D: set[int], d: int, delta: int, independent: bool = False) -> dict:
    A, c = construction(D, d, delta)
    rec = inspect_tail(A, c)
    k, M = len(D), 4*d+1+delta
    expected_pf = sorted((set(range(M-2*d, M)) - {M-a for a in D if a}) |
                         {M+1+a for a in set(range(2*d+1))-D} | {2*M+1})
    require(rec['g'] == 6*d+3-k+delta, 'Genus formula fails')
    require(rec['t'] == 4*d+3-2*k, 'Type formula fails')
    require(rec['pseudo_frobenius'] == expected_pf, 'PF-set formula fails')
    require(rec['leaf'] and rec['generators'] == A, 'Leaf/generator formula fails')
    if independent:
        other = from_generators(A)
        for key in ('m', 'F', 'g', 't', 'pseudo_frobenius', 'generators', 'leaf'):
            require(rec[key] == other[key], f'Independent reconstruction differs: {key}')
    return rec


def tree_checks(max_genus: int) -> list[dict]:
    """Enumerate all semigroups through max_genus by deleting effective generators."""
    level = [2]  # the unique genus-one gap set {1}
    output = []
    for g in range(1, max_genus+1):
        nxt = []
        leaf_count, max_type = 0, 0
        for G in level:
            F = G.bit_length()-1
            m = 1
            while (G >> m) & 1:
                m += 1
            children = []
            for n in range(F+1, F+m+1):
                if not any(not ((G >> a) & 1) and not ((G >> (n-a)) & 1)
                           for a in range(m, n//2+1)):
                    children.append(n)
            if not children:
                leaf_count += 1
                ng = ((1 << (F+1))-2) ^ G
                t = sum(1 for p in range(1, F+1) if (G >> p) & 1 and
                        not ((ng << p) & G))
                max_type = max(max_type, t)
                h = 2*g-3*t
                require(3*t+3 <= 2*g and h*h >= 4*t-3, 'Universal bound failure')
                require(t <= conjectured_bound(g), 'Old conjecture fails in small-genus run')
            if g < max_genus:
                nxt.extend(G | (1 << n) for n in children)
        output.append(dict(genus=g, semigroups=len(level), leaves=leaf_count,
                           maximum_leaf_type=max_type))
        level = nxt
    known = {1: 1, 2: 2, 3: 4, 10: 204, 15: 2857, 20: 37396}
    for row in output:
        if row['genus'] in known:
            require(row['semigroups'] == known[row['genus']], 'Tree count sanity check fails')
    return output


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open('w', newline='', encoding='utf-8') as file:
        writer = csv.DictWriter(file, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parent.parent/'data')
    parser.add_argument('--tree-genus', type=int, default=20)
    args = parser.parse_args()
    require(1 <= args.tree_genus <= 24, 'Choose a tree genus between 1 and 24')
    args.out.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()

    D = {0, 1, 3, 5, 6}
    cert = family_record(D, 6, 0, independent=True)
    cert['apery'] = from_generators(cert['generators'])['apery']
    require((cert['g'], cert['t'], cert['violation']) == (34, 17, 1), 'Main claim fails')
    A = cert['generators']
    cert['tail_decompositions'] = {str(n): next([a, n-a] for a in A if n-a in A)
                                   for n in range(cert['c'], cert['c']+cert['m'])}
    G = set(cert['gaps'])
    cert['non_pf_witnesses'] = {str(p): next(a for a in A if p+a in G)
                              for p in G-set(cert['pseudo_frobenius'])}
    (args.out/'counterexample.json').write_text(json.dumps(cert, indent=2)+'\n')

    rows = []
    family_instances = 0
    for q in range(1, 101):
        d = 2*q
        D = {0, d} | set(range(1, d, 2))
        rec = family_record(D, d, 0, independent=q <= 15)
        if q >= 3:
            require(rec['violation'] >= 1, 'Linear-family counterexample fails')
        rows.append(dict(family='odd_progression', parameter=q, d=d, basis_size=len(D),
                         genus=rec['g'], type=rec['t'], conjectured_bound=rec['conjectured_bound'],
                         violation=rec['violation']))
        family_instances += 1
    for r in range(1, 31):
        d = r*r
        D = set(range(r)) | set(range(0, d+1, r)) | set(range(d-r+1, d+1))
        require(len(D) == 3*r-1, 'Grid-basis cardinality fails')
        for delta in (0, 1, 7, 12*r+2):
            rec = family_record(D, d, delta, independent=(r <= 10 and delta == 0))
            family_instances += 1
            if delta == 0:
                rows.append(dict(family='square_grid', parameter=r, d=d, basis_size=len(D),
                                 genus=rec['g'], type=rec['t'], conjectured_bound=rec['conjectured_bound'],
                                 violation=rec['violation']))
                if r >= 4:
                    require(rec['violation'] > 0, 'Grid-family counterexample fails')
    write_csv(args.out/'families.csv', rows)

    basis_rows = []
    arbitrary_instances = 0
    for d in range(1, 13):
        count = 0
        for mask in range(1 << (d-1)):
            D = {0, d} | {i for i in range(1, d) if (mask >> (i-1)) & 1}
            if not is_basis(D, d):
                continue
            count += 1
            for delta in (0, 1, 7):
                family_record(D, d, delta)
                arbitrary_instances += 1
        basis_rows.append(dict(maximum=d, restricted_bases=count))
    write_csv(args.out/'restricted_bases.csv', basis_rows)
    tree = tree_checks(args.tree_genus)
    write_csv(args.out/'tree_checks.csv', tree)
    report = dict(status='PASS', python=sys.version.split()[0], platform=platform.platform(),
                  main_counterexample=dict(genus=34, type=17, multiplicity=26,
                                           frobenius=51, conjectured_bound=16),
                  explicit_family_instances=family_instances,
                  arbitrary_basis_instances=arbitrary_instances,
                  restricted_bases=sum(x['restricted_bases'] for x in basis_rows),
                  independent_dijkstra_reconstructions=26,
                  exhaustive_tree_max_genus=args.tree_genus,
                  exhaustive_tree_semigroups=sum(row['semigroups'] for row in tree),
                  exhaustive_tree_leaves=sum(row['leaves'] for row in tree),
                  elapsed_seconds=round(time.perf_counter()-start, 3),
                  qualification='Finite exact-arithmetic checks; infinite assertions have written proofs. '
                                'No independent exhaustive minimality check through genus 33.')
    (args.out/'verification_report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
