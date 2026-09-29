#!/usr/bin/env python3
"""Exact finite checks for the three-output binary reversal article.

Standard-library Python 3.10+. These checks complement, not replace,
the all-n proof in article.tex. No assertion depends on floating point.
"""
from __future__ import annotations
import argparse
import csv
import json
from collections import deque
from itertools import product
from math import gcd, factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def product_bound(r: int) -> int:
    """Largest product of positive parts of a partition of r; J(0)=1."""
    if r < 0:
        raise ValueError('Negative residual size')
    if r <= 1:
        return 1
    q, rem = divmod(r, 3)
    if rem == 0:
        return 3 ** q
    if rem == 1:
        return 4 * 3 ** (q - 1)
    return 2 * 3 ** q


def optimal_split(n: int) -> tuple[int, int]:
    if n < 7:
        raise ValueError('The all-n split is defined for n >= 7')
    h = n // 2
    if n % 2:
        return h, h + 1
    delta = 1 if h % 2 == 0 else 2
    return h - delta, h + delta


def bipartite_count(a: int, b: int) -> int:
    return 3 * (2 ** a + 2 ** b - 2)


def defect(n: int) -> int:
    a, b = optimal_split(n)
    return bipartite_count(a, b) - b


def reversal_max(n: int) -> int:
    if n in {3, 4, 5, 6}:
        return {3: 24, 4: 67, 5: 218, 6: 699}[n]
    return 3 ** n - defect(n)


def candidates(n: int):
    """Conservative structural deficits. Uses J(r), not exact order sets."""
    yield 'nonsurjective', (), 3 ** n - 2 ** n
    q, z = divmod(n, 3)
    multinomial = factorial(n) // (factorial(q) ** (3-z) * factorial(q+1) ** z)
    yield 'permutations', (), 3 ** n - multinomial
    yield 'singulars', (), 4 * 3 ** (n - 2) - 1
    for m in range(2, n + 1):
        r = n - m
        for d in range(1, m):
            if m % d:
                continue
            ell = m // d
            p = (2 ** ell + 2 * (-1) ** ell) ** d * 3 ** r
            yield 'cycle', (m, d, r), p - m * product_bound(r)
    for a in range(1, n // 2 + 1):
        for b in range(a, n - a + 1):
            d = gcd(a, b)
            r = n - a - b
            p = bipartite_count(a // d, b // d) ** d * 3 ** r
            order = (b if d == 1 else a * b // d) * product_bound(r)
            yield 'bipartite', (a, b, d, r), p - order


def witness(n: int):
    """The parity-version U_(a,b) witness used by the repository."""
    a, b = optimal_split(n)
    p = tuple(list(range(1, a)) + [0] + list(range(a + 1, n)) + [a])
    s = list(range(n))
    s[0], s[n-1] = a, 0
    if a % 2:
        s[1], s[2] = s[2], s[1]
    tau = (0,) * a + (1,) + (2,) * (b-1)
    return p, tuple(s), tau


def orbit(tau, letters, limit=2_000_000):
    seen = {tuple(tau)}
    queue = deque(seen)
    while queue:
        c = queue.popleft()
        for t in letters:
            v = tuple(c[i] for i in t)
            if v not in seen:
                if len(seen) >= limit:
                    raise RuntimeError('Orbit limit exceeded; no partial count is returned')
                seen.add(v)
                queue.append(v)
    return seen


def accessible(letters, initial=0):
    seen = {initial}
    todo = [initial]
    while todo:
        q = todo.pop()
        for t in letters:
            if t[q] not in seen:
                seen.add(t[q]); todo.append(t[q])
    return len(seen) == len(letters[0])


def proper(c, a):
    return set(c[:a]).isdisjoint(c[a:])


def primitive_binary_count(d):
    # Recurrence subtracts all words with smaller divisor periods.
    count = [0] * (d + 1)
    for j in range(1, d+1):
        count[j] = 2 ** j - sum(count[e] for e in range(1, j) if j % e == 0)
    return count[d]


def orbit_inventory(a, b):
    # Direct enumeration is used only for the small inventory audit.
    n = a + b
    p = tuple(list(range(1, a)) + [0] + list(range(a+1, n)) + [a])
    unseen = {c for c in product(range(3), repeat=n) if proper(c, a)}
    inventory = {}
    while unseen:
        c = next(iter(unseen))
        o = orbit(c, (p,))
        require(o <= unseen, 'Overlapping permutation orbits')
        unseen.difference_update(o)
        inventory[len(o)] = inventory.get(len(o), 0) + 1
    expected = {1: 6}
    for d in range(2, max(a,b)+1):
        coefficient = int(a % d == 0) + int(b % d == 0)
        if coefficient:
            expected[d] = 3 * primitive_binary_count(d) * coefficient // d
    require(inventory == expected, f'Inventory failure at {a,b}')
    return inventory


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--max-n', type=int, default=200)
    ap.add_argument('--bfs-max-n', type=int, default=11)
    args = ap.parse_args()
    if not 7 <= args.max_n <= 500 or not 7 <= args.bfs_max_n <= 12:
        ap.error('Use 7 <= max-n <= 500 and 7 <= bfs-max-n <= 12')
    data = ROOT / 'data'; data.mkdir(exist_ok=True)
    rows = []
    candidate_checks = 0
    for n in range(7, args.max_n+1):
        a, b = optimal_split(n)
        require(1 < a < b and a+b == n and gcd(a,b) == 1, 'Split conditions')
        allowed = [(bipartite_count(x,n-x)-(n-x),x,n-x)
                   for x in range(1,(n+1)//2) if gcd(x,n-x)==1]
        require(min(allowed) == (defect(n),a,b), 'Coprime optimization')
        entries = list(candidates(n)); candidate_checks += len(entries)
        best = min(entries, key=lambda c: c[2])
        require(best[2] == defect(n), f'Structural bound fails at n={n}: {best}')
        equals = [(kind,params) for kind,params,d in entries if d==defect(n)]
        require(equals == [('bipartite',(a,b,1,0))], f'Rigidity fails at n={n}')
        rows.append({'n':n,'a':a,'b':b,'defect':defect(n),'maximum':reversal_max(n),
                     'candidates':len(entries)})
    with (data / 'structural_checks.csv').open('w',newline='') as out:
        writer=csv.DictWriter(out,fieldnames=rows[0]);writer.writeheader();writer.writerows(rows)
    # Verify the finite same-cycle table used by the proof itself.
    small_cycle=[]
    for n in range(7,13):
        value=min((d,params) for kind,params,d in candidates(n) if kind=='cycle')
        small_cycle.append({'n':n,'minimum':value[0],'parameters':value[1]})
    require([r['minimum'] for r in small_cycle] == [102,250,207,639,1926,1284],
            'Same-cycle table changed')
    # Integer form of the sole exponential threshold inequality.
    require(9**13 * 2**6 > 51**6 * 2**13, 'n=13 threshold')
    bfs=[]
    for n in range(7,args.bfs_max_n+1):
        p,s,tau=witness(n);a,b=optimal_split(n)
        o=orbit(tau,(p,s));require(accessible((p,s)), 'Inaccessible witness')
        require(len(o)==reversal_max(n), f'Witness count n={n}')
        pure=orbit(tau,(p,));require(len(pure)==b,'Wrong pure period')
        # Every proper state lies in pure; every improper coloring is reached.
        missing=[c for c in product(range(3),repeat=n) if c not in o]
        require(len(missing)==defect(n),'Missing count')
        require(all(proper(c,a) for c in missing),'An improper state is missing')
        require({c for c in o if proper(c,a)}==pure,'Proper orbit mismatch')
        bfs.append({'n':n,'p':p,'s':s,'tau':tau,'orbit_size':len(o),
                    'missing':len(missing),'proper_orbit_size':len(pure)})
    # A rank-(n-2) map with two cross collisions: every one-cross-pair coloring is absent.
    a,b=3,4;n=a+b;p,_,tau=witness(n)
    s=list(range(n));s[a]=0;s[a+1]=1
    o=orbit(tau,(p,tuple(s)))
    targets=[c for c in product(range(3),repeat=n)
             if sum(c[i]==c[j] for i in range(a) for j in range(a,n))==1]
    require(len(targets)==6*a*b,'One-cross-pair count')
    require(all(c not in o for c in targets),'Rank penalty failure')
    inventories={f'{a},{b}':orbit_inventory(a,b) for a,b in [(3,4),(3,5),(4,5)]}
    summary={'status':'PASS','max_n':args.max_n,'parameter_pairs':len(rows),
             'structural_candidates_checked':candidate_checks,'same_cycle_table':small_cycle,
             'bfs_witnesses':bfs,'proper_orbit_inventories':inventories,
             'rank_penalty_targets_checked':len(targets),
             'threshold_check':'9^13 * 2^6 > 51^6 * 2^13',
             'scope':'Finite exact checks; not a proof-assistant certificate of the all-n theorem.'}
    (data/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
