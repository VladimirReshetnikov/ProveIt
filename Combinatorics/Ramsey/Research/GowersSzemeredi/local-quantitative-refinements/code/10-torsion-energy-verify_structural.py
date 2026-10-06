"""Exact finite checks of the two structural proof mechanisms.

This is a check of finite examples, not a substitute for the proofs.
No third-party packages are needed.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product


def addset(X, Y, p):
    return {((x[0] + y[0]) % p, (x[1] + y[1]) % p)
            for x in X for y in Y}


def check_fibre(B, values, p, k):
    phi = dict(zip(B, values))
    graph = set(phi.items())
    kgraph = {(0, 0)}
    for _ in range(k):
        kgraph = addset(kgraph, graph, p)
    H = {(x[1] - y[1]) % p for x in kgraph for y in kgraph
         if x[0] == y[0]}
    h = len(H)
    if h == 1:
        selected = B
    else:
        a = k * (h - 1)
        L = (p - 2) // a
        assert Fraction(L + 1, p) >= Fraction(1, a + 1)
        d = next(d for d in range(1, p)
                 if all((j * d) % p not in H
                        for j in range(1, k * L + 1)))
        candidates = [tuple(x for x in B
                            if phi[x] in {(b + d * j) % p
                                          for j in range(L + 1)})
                      for b in range(p)]
        selected = max(candidates, key=len)
    assert len(selected) * (k * (h - 1) + 1) >= len(B)
    sums = {}
    for xs in product(selected, repeat=k):
        xsum = sum(xs) % p
        ysum = sum(phi[x] for x in xs) % p
        assert sums.setdefault(xsum, ysum) == ysum
    differences = {((x[0] - y[0]) % p, (x[1] - y[1]) % p)
                   for x in graph for y in graph}
    C = Fraction(len(differences), len(B))
    assert h <= C ** (2 * k + 1)


def check_weighted_counts(A, p):
    m = len(A)
    r = Counter((a - b) % p for a in A for b in A)
    energy = sum(v * v for v in r.values())
    assert sum(r[(a - b) % p] for a in A for b in A) == energy
    Q = Counter()
    for u, ru in r.items():
        for v, rv in r.items():
            Q[(u - v) % p] += ru * rv
    T = {(a, b): sum(r[(a - z) % p] * r[(b - z) % p] for z in A)
         for a in A for b in A}
    for a in A:
        for b in A:
            assert Q[(a - b) % p] >= T[a, b]
    R8 = Counter()
    for u, qu in Q.items():
        for v, qv in Q.items():
            R8[(u - v) % p] += qu * qv
    assert sum(R8.values()) == m ** 8
    for a in A:
        for b in A:
            assert R8[(a - b) % p] >= sum(T[a, z] * T[b, z] for z in A)


def main():
    fibre_cases = 0
    weighted_cases = 0
    for p in (2, 3, 5):
        for m in range(1, p + 1):
            for B in combinations(range(p), m):
                check_weighted_counts(B, p)
                weighted_cases += 1
                for values in product(range(p), repeat=m):
                    for k in (1, 2, 3):
                        check_fibre(B, values, p, k)
                        fibre_cases += 1
    print(f"PASS: {fibre_cases} exhaustive fibre instances over F_2, F_3, F_5")
    print(f"PASS: {weighted_cases} exact weighted/eight-tuple count instances")


if __name__ == "__main__":
    main()
