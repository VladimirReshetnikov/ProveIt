"""Check the local cost inequality using an exact minimum-weight vertex cover.

The retained sets are independent sets in a 3-uniform hypergraph. Deleting
one member of every geometric progression is equivalent to taking a vertex
cover. All optimization arithmetic here is integer arithmetic.
"""
from fractions import Fraction as F
from pathlib import Path
from math import isqrt, lcm
from itertools import combinations

N = 10**6
TAX = F(83,1000)
MARGIN = F(23,10000)
PRIMES = (2,3,5)


def smooth_records():
    records = []
    for i in range(N.bit_length()):
        two = 2**i
        for j in range(N.bit_length()):
            base = two * 3**j
            if base > N:
                break
            for k in range(N.bit_length()):
                n = base * 5**k
                if n > N:
                    break
                records.append((n,(i,j,k)))
    return sorted(records)


def allowed_digits(k):
    # Explicit first four ternary digits suffice, since k <= 19.
    return k in {a+3*b+9*c+27*d for a in (0,1) for b in (0,1)
                                for c in (0,1) for d in (0,1)}


def integer_edges(ns):
    values = set(ns)
    return {tuple(sorted((a,a*r,a*r*r))) for a in ns
            for r in range(2,1+isqrt(N//a)) if a*r*r in values and a*r in values}



def construct_s(records):
    ns = [n for n,_ in records]
    edges = integer_edges(ns)
    pairs = {v:[] for v in ns}
    for edge in edges:
        for v in edge:
            pairs[v].append(set(edge)-{v})
    s = {60,90,150,180,300,450,900}
    for n,exponents in records:
        if all(map(allowed_digits,exponents)) and not any(e <= s for e in pairs[n]):
            s.add(n)
    assert all(not set(e)<=s for e in edges)
    return s


def check():
    records = smooth_records()
    ns = [n for n,_ in records]
    s = construct_s(records)
    assert s == set(map(int, Path(__file__).with_name("replacement.txt").read_text().split()))
    tail = F(15,4) - sum(F(1,n) for n in ns)
    goal = (1-TAX)*sum(F(1,n) for n in s) - tail - MARGIN
    den = 1000*lcm(*ns)
    weights = [((1-TAX) if n in s else 1)*F(den,n) for n in ns]
    assert all(w.denominator == 1 for w in weights)
    weights = list(map(int,weights))
    # Prove total weight of deletions >= required.
    cover = F(sum(weights)) - goal*den
    required = -(-cover.numerator//cover.denominator)

    # Enumerate rational progressions by their endpoints, independently
    # of the middle/left enumeration in the direct independent-set check.
    index = {n:i for i,n in enumerate(ns)}
    edges = []
    for i,j in combinations(range(len(ns)),2):
        v = ns[i]*ns[j]
        m = isqrt(v)
        if m*m==v and m in index:
            edges.append((i,index[m],j))
    edges.sort(key=lambda e:min(weights[i] for i in e),reverse=True)

    visits = 0
    def branch(edges, need):
        nonlocal visits
        visits += 1
        if need <= 0:
            return True
        # Fractional matching dual: assign each edge its minimum residual
        # vertex capacity. This lower-bounds the cost of any cover.
        capacity = dict(enumerate(weights))
        accumulated = 0
        for e in edges:
            take = min(capacity[v] for v in e)
            if take:
                for v in e:
                    capacity[v] -= take
                accumulated += take
                if accumulated >= need:
                    return True
        if not edges:
            return False
        edge = edges[0]
        for v in reversed(edge):
            if not branch([e for e in edges if v not in e],need-weights[v]):
                return False
        return True

    assert branch(edges,required)
    print('Smooth records, integer competitor size, rational hyperedges:',len(ns),len(s),len(edges))
    print('Cover recursion nodes:',visits)
    print('Required local exchange gain after tax and tail: at least', MARGIN)


if __name__ == '__main__':
    check()
