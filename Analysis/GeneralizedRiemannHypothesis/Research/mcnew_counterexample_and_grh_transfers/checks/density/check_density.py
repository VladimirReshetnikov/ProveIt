"""Verify both density bounds. Run with Python 3.9+ and no external packages."""
import csv
import gzip
import json
from fractions import Fraction as Q
from math import prod
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = (2, 3, 5, 7)
FIVE = BASE + (11,)


def smooth_numbers(primes, limit):
    values = [1]
    for p in primes:
        for seed in values.copy():
            while seed <= limit // p:
                seed *= p
                values.append(seed)
    return sorted(values)


def triple_free(values):
    values = sorted(values)
    lookup = set(values)
    for j, b in enumerate(values):
        for a in values[:j]:
            if b*b % a == 0 and b*b//a in lookup:
                raise ValueError(f"geometric progression {a},{b},{b*b//a}")


def prime(n):
    return n >= 2 and all(n % i for i in range(2, n) if i*i <= n)


def lower_bound():
    thresholds = []
    last_count = last_t = 0
    integral = Q(0)
    allowed = set(smooth_numbers(BASE, 10**6))
    with (ROOT/'lower.csv').open() as file:
        for row in csv.reader(file):
            t, *values = map(int, row)
            assert last_t < t <= 10**6
            assert last_count + 1 == len(values) == len(set(values))
            assert set(values) <= allowed and max(values) <= t
            triple_free(values)
            integral += Q(len(values)-last_count, t)
            last_t, last_count = t, len(values)
            thresholds.append(t)
    # c_P * product_{p outside P}(1-p^-2) = (6/pi^2)*product_{p in P} p/(p+1).
    # For primes 11..997, exponents 0,1,3,4 enlarge the factor by 1+p^-3.
    # Alternating sums in Machin's formula give an exact rational upper bound on pi.
    def atan_partial(q, terms):
        return sum(Q((-1)**j, (2*j+1)*q**(2*j+1)) for j in range(terms))
    assert 16*atan_partial(5, 5) - 4*atan_partial(239, 2) < Q(355, 113)
    core = Q(6*113**2, 355**2) * prod(Q(p, p+1) for p in BASE)
    core *= prod(1+Q(1,p**3) for p in range(11, 998) if prime(p))
    lower = core*integral
    print("Thresholds:", len(thresholds), "last:", last_t, "size:", last_count)
    print("Template integral:", integral)
    print("Certified lower bound:", float(lower), "(display rounded)")
    return lower


def hypergraph(limit):
    values = smooth_numbers(FIVE, limit)
    index = {x: i for i, x in enumerate(values)}
    edges = [(index[a],index[b],index[b*b//a]) for b in values for a in values
             if a < b and b*b % a == 0 and b*b//a in index]
    return values, edges


def check_tree(limit, cap):
    values, edges = hypergraph(limit)
    with gzip.open(ROOT/'trees'/f'tree{limit}.json.gz','rt') as file:
        tree = json.load(file)
    calls = 0

    def verify(node, deleted, retained):
        nonlocal calls
        calls += 1
        tag = node[0]
        budget = len(values)-cap-1-len(deleted)
        if tag == 'k':
            assert budget < 0
        elif tag == 'x':
            assert set(edges[node[1]]) <= retained
        elif tag == 'l':
            total = 0
            loads = [0]*len(values)
            for i, weight in node[1]:
                assert 0 <= i < len(edges) and type(weight) is int and weight > 0
                edge = set(edges[i])
                assert not edge & deleted
                for v in edge-retained:
                    loads[v] += weight
                total += weight
            assert total > budget*max(loads)
        else:
            assert type(tag) is int and 0 <= tag < len(values)
            assert tag not in (deleted | retained) and len(node)==3
            verify(node[1], deleted | {tag}, retained)
            verify(node[2], deleted, retained | {tag})
    verify(tree,set(),set())
    return calls


def upper_bound():
    intervals = json.loads((ROOT/'intervals.json').read_text())
    mass = Q(0)
    last = 0
    for row in intervals:
        a,b = row['left'],row['right']
        end = row['max_smooth']
        cap = row['cap']
        assert last <= a < b and smooth_numbers(FIVE,b-1)[-1] == end
        last=b
        sets = row['layers']
        for j, block in enumerate(sets):
            assert len(block)==len(set(block))
            assert set(block) <= set(smooth_numbers(BASE,a//11**j))
            triple_free(block)
        gain=sum(map(len,sets))-cap
        assert gain>0
        nodes=check_tree(end,cap)
        print(f"[{a},{b}) cap {cap}, advantage {gain}, tree nodes {nodes}")
        mass += gain*(Q(1,a)-Q(1,b))
    deficit = prod(Q(p-1,p) for p in FIVE)*mass
    assert deficit == Q(64,139755)
    # McNew, sec. 4, publishes the strict bound on the 7-smooth optimum.
    upper=Q(772059,10**6)-deficit
    print("7-smooth minus 11-smooth at least", deficit)
    print("Upper estimate:", upper, float(upper), "(decimal rounded)")
    return upper


if __name__=='__main__':
    low = lower_bound()
    high = upper_bound()
    assert low > Q(7365954, 10**7) and high < Q(7716011, 10**7)
