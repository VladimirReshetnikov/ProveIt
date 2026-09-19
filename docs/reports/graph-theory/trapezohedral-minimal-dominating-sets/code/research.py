#!/usr/bin/env python3
"""Exact enumeration, independent checks, and uniform sampling for A381190.

Requires Python 3.9+ and only the standard library. Vertex labels are N=0,
S=1, a_i=2+2*i, b_i=3+2*i. Counts are of vertex subsets, not isomorphism classes.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import random
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterator, List, Optional, Set, Tuple

ROOT = Path(__file__).resolve().parents[1]
OEIS_TERMS = [6,16,30,36,70,96,144,220,308,456,650,924,1320,1856,2618,
              3672,5130,7160,9954,13816,19136,26448,36500,50284,69174,
              95032,130384,178680,244590,334464,456918,623628,850430,
              1158768,1577680,2146468,2918292,3965040,5383874,7306068]


def require_n(n: int) -> None:
    if not isinstance(n, int) or n < 3:
        raise ValueError("n must be an integer >= 3")


def compositions(maximum: int) -> List[int]:
    """p[m] counts ordered compositions of m with parts 2 and 3."""
    if maximum < 0:
        raise ValueError("maximum must be nonnegative")
    p = [0] * (maximum + 1)
    p[0] = 1
    for m in range(1, maximum + 1):
        p[m] = (p[m-2] if m >= 2 else 0) + (p[m-3] if m >= 3 else 0)
    return p


def choose(n: int, k: int) -> int:
    return math.comb(n, k) if 0 <= k <= n else 0


def refined_counts(n: int) -> Dict[int, Tuple[int, int]]:
    """Return {size: (tree count, unicyclic count)} by exact binomial formulas."""
    require_n(n)
    result = {}
    for k in range((n+2)//3, n//2+1):
        t = n-2*k
        result[n-k+2] = (4*n*choose(k-1, t), 2*n*choose(k-1, t-1))
    return dict(sorted(result.items()))


def total(n: int) -> int:
    require_n(n)
    p = compositions(n)
    return 2*n*(2*p[n-2]+p[n-3])


def graph(n: int) -> List[int]:
    """Return open-neighborhood bit masks directly from the graph definition."""
    require_n(n)
    adj = [0] * (2*n+2)
    def edge(i: int, j: int) -> None:
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    for i in range(n):
        a, b, nxt = 2+2*i, 3+2*i, 2+2*((i+1)%n)
        edge(0, a); edge(1, b); edge(a, b); edge(b, nxt)
    return adj


def bit_indices(mask: int) -> Iterator[int]:
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask ^= low


def independent_test(adj: List[int], d: int) -> bool:
    """Test connected minimal domination using graph operations only."""
    if d <= 0 or d >= (1 << len(adj)):
        return False
    private = 0
    for w, neighbors in enumerate(adj):
        hit = (neighbors | (1 << w)) & d
        if not hit:
            return False
        if hit & (hit-1) == 0:
            private |= hit
    if private != d:
        return False
    seen = frontier = d & -d
    while frontier:
        low = frontier & -frontier
        frontier ^= low
        fresh = adj[low.bit_length()-1] & d & ~seen
        seen |= fresh
        frontier |= fresh
    return seen == d


def eligible_edges(x: List[int]) -> List[int]:
    """Indices j of eligible cyclic edges (j,j+1), or [] for an illegal word."""
    n = len(x)
    if any(x[i] == x[(i+1)%n] == 0 for i in range(n)):
        return []
    if any(x[i] == x[(i+1)%n] == x[(i+2)%n] == 1 for i in range(n)):
        return []
    out = []
    for j in range(n):
        left, right = x[j], x[(j+1)%n]
        if left == right == 1:
            out.append(j)
        elif left == 1 and right == 0 and x[(j-1)%n] == 0:
            out.append(j)
        elif left == 0 and right == 1 and x[(j+2)%n] == 0:
            out.append(j)
    return out


def hub_exchange(n: int, d: int) -> int:
    """Graph automorphism N<->S, a_i -> b_(-i), b_i -> a_(-i)."""
    out = ((d & 1) << 1) | ((d & 2) >> 1)
    for i in range(n):
        if d & (1 << (2+2*i)):
            out |= 1 << (3+2*((-i)%n))
        if d & (1 << (3+2*i)):
            out |= 1 << (2+2*((-i)%n))
    return out


def structural_sets(n: int) -> Set[int]:
    """Enumerate from the binary-word classification, not from domination."""
    require_n(n)
    result = set()
    for word in range(1 << n):
        x = [(word >> i) & 1 for i in range(n)]
        for j in eligible_edges(x):
            d = 1 | (1 << (3+2*j))
            for i, selected in enumerate(x):
                if selected:
                    d |= 1 << (2+2*i)
            result.add(d)
            result.add(hub_exchange(n, d))
    return result


def sample(n: int, rng: Optional[random.Random] = None) -> Set[int]:
    """Exactly uniform sample; every choice uses integers, never rounded weights.

    The rooted-gap construction represents each zero set exactly k times.
    Python's randrange performs an unbiased integer draw.
    """
    require_n(n)
    rng = rng if rng is not None else random.SystemRandom()
    weights = []
    for k in range((n+2)//3, n//2+1):
        t = n-2*k
        weight = 2*n*(2*choose(k-1, t)+choose(k-1, t-1))
        weights.append((k, weight))
    target = rng.randrange(sum(w for _, w in weights))
    k = weights[-1][0]
    for candidate, weight in weights:
        if target < weight:
            k = candidate
            break
        target -= weight
    s, t = 3*k-n, n-2*k
    gaps = [2]*s+[3]*t
    rng.shuffle(gaps)  # Every distinct multiset permutation has equal multiplicity.
    root = rng.randrange(n)
    zeros = set()
    at = root
    for gap in gaps:
        zeros.add(at)
        at = (at+gap)%n
    assert at == root and len(zeros) == k
    x = [int(i not in zeros) for i in range(n)]
    j = rng.choice(eligible_edges(x))
    d = 1 | (1 << (3+2*j))
    for i, selected in enumerate(x):
        if selected:
            d |= 1 << (2+2*i)
    if rng.randrange(2):
        d = hub_exchange(n, d)
    return set(bit_indices(d))


def verify(exhaustive_csv: Optional[Path] = None) -> dict:
    p = compositions(1000)
    checks = {}
    assert [2*n*(2*p[n-2]+p[n-3]) for n in range(3, 43)] == OEIS_TERMS
    checks['published_terms_matched'] = len(OEIS_TERMS)
    previous = {}
    for n in range(3, 1001):
        f = refined_counts(n)
        previous[n] = f
        fm2, fm3 = previous.get(n-2, {}), previous.get(n-3, {})
        assert sum(t+u for t,u in f.values()) == 2*n*(2*p[n-2]+p[n-3])
        assert sum(t for t,u in f.values()) == 4*n*p[n-2]
        assert sum(u for t,u in f.values()) == 2*n*p[n-3]
        values = [t+u for t,u in f.values()]
        assert all(values[i]**2 > values[i-1]*values[i+1]
                   for i in range(1, len(values)-1))
        low, high = min(f), max(f)
        assert low == (n+1)//2+2 and high == 2*n//3+2
        assert sum(f[low]) == (4*n if n%2 == 0 else 2*n*(n-2))
        m, r = divmod(n,3)
        maximum_count = [2*n, n*m*(m+3), 2*n*(m+2)][r]
        assert sum(f[high]) == maximum_count
        for d, (t,u) in f.items():
            assert (t+u) % (2*n) == 0
            if n >= 6:
                lhs = (t+u)//(2*n)
                rhs = sum(fm2.get(d-1, (0,0)))//(2*(n-2))
                rhs += sum(fm3.get(d-2, (0,0)))//(2*(n-3))
                assert lhs == rhs
    checks['exact_formula_recurrence_extrema_logconcavity_range'] = [3, 1000]
    for n in range(3, 8):
        adj = graph(n)
        brute = {d for d in range(1 << len(adj)) if independent_test(adj, d)}
        assert brute == structural_sets(n)
    checks['independent_python_set_level_exhaustion_range'] = [3, 7]
    if exhaustive_csv is not None:
        found = defaultdict(set)
        sizes = defaultdict(Counter)
        with exhaustive_csv.open(newline='', encoding='utf-8-sig') as inp:
            for row in csv.DictReader(inp):
                n,d,e,mask = (int(row[x]) for x in ('n','size','edges','mask'))
                assert e in (d-1,d)
                found[n].add(mask)
                sizes[n][d,e-d+1] += 1
        assert found
        assert sorted(found) == list(range(3, max(found)+1))
        for n, masks in sorted(found.items()):
            assert masks == structural_sets(n)
            for d, (t,u) in refined_counts(n).items():
                assert sizes[n][d,0] == t and sizes[n][d,1] == u
        checks['independent_cpp_set_level_exhaustion_range'] = [min(found),max(found)]
        checks['cpp_subsets_examined'] = sum(1 << (2*n+2) for n in found)
        checks['cpp_accepted_by_n'] = {n:len(found[n]) for n in sorted(found)}
    rng = random.Random(381190)
    for n in [3,4,5,6,7,10,20,50,100]:
        adj = graph(n)
        for _ in range(100):
            d = sum(1 << v for v in sample(n, rng))
            assert independent_test(adj, d)
    checks['sampled_sets_independently_validated'] = 900
    return checks


def write_data(maximum: int) -> None:
    require_n(maximum)
    directory = ROOT/'data'
    directory.mkdir(exist_ok=True)
    p = compositions(maximum)
    with (directory/'counts.csv').open('w', newline='') as out:
        w = csv.writer(out)
        w.writerow(['n','a_n','a_n_over_2n','tree_count','unicyclic_count'])
        for n in range(3, maximum+1):
            t,u = 4*n*p[n-2],2*n*p[n-3]
            w.writerow([n,t+u,(t+u)//(2*n),t,u])
    with (directory/'b381190.txt').open('w') as out:
        out.write('# A381190: independently computed by the proved formula.\n')
        out.write('# n >= 3; generated by code/research.py.\n')
        for n in range(3, maximum+1):
            out.write(f'{n} {2*n*(2*p[n-2]+p[n-3])}\n')
    with (directory/'size_distribution.csv').open('w', newline='') as out:
        w = csv.writer(out)
        w.writerow(['n','size','k_zeros','trees','unicyclic','total'])
        for n in range(3, min(maximum,100)+1):
            for d,(t,u) in refined_counts(n).items():
                w.writerow([n,d,n-d+2,t,u,t+u])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    v = sub.add_parser('verify')
    v.add_argument('--exhaustive-csv', type=Path)
    v.add_argument('--report', type=Path)
    data = sub.add_parser('data')
    data.add_argument('--maximum', type=int, default=1000)
    s = sub.add_parser('sample')
    s.add_argument('n', type=int)
    s.add_argument('--seed', type=int)
    args = parser.parse_args()
    if args.command == 'verify':
        report = verify(args.exhaustive_csv)
        text = json.dumps(report, indent=2)+'\n'
        if args.report:
            args.report.write_text(text)
        print(text, end='')
    elif args.command == 'data':
        write_data(args.maximum)
    else:
        print(sorted(sample(args.n, random.Random(args.seed) if args.seed is not None else None)))

if __name__ == '__main__':
    main()
