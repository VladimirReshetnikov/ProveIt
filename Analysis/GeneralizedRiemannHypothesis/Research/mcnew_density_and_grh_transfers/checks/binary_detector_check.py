#!/usr/bin/env python3
"""Exhaust binary detectors by exact convolution, without character tables.

Standard-library Python. The positive-definiteness check uses fraction-free
elimination: its successive diagonal pivots are the leading principal minors.
"""
from itertools import permutations, combinations

def compose(p, q):
    return tuple(p[i] for i in q)

def parity(p):
    return sum(a > b for a, b in combinations(p, 2)) % 2

def group(name):
    if name == "S3xC2":
        elts = [(p, t) for p in permutations(range(3)) for t in (0, 1)]
        def mul(x, y):
            return compose(x[0], y[0]), x[1] ^ y[1]
    else:
        n = 4
        elts = [p for p in permutations(range(n))
                if name == "S4" or parity(p) == 0]
        mul = compose
    index = {g: i for i, g in enumerate(elts)}
    return [[index[mul(x, y)] for y in elts] for x in elts]

def products(U, V, table):
    return {table[u][v] for u in U for v in V}

def positive_definite(matrix):
    # For a symmetric matrix, Sylvester's criterion needs positive pivots.
    a = [row[:] for row in matrix]
    prev = 1
    for k in range(len(a)):
        pivot = a[k][k]
        if pivot <= 0:
            return False
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                num = pivot * a[i][j] - a[i][k] * a[k][j]
                assert num % prev == 0
                a[i][j] = num // prev
        prev = pivot
    return True

def check(name):
    tab = group(name)
    ids = range(len(tab))
    inv = [row.index(0) for row in tab]
    comm = {tab[tab[inv[x]][inv[y]]][tab[x][y]] for x in ids for y in ids}
    H = {0}
    while True:
        extended = H | products(H, comm, tab)
        if H == extended:
            break
        H = extended
    cosets = sorted({tuple(sorted(products({x}, H, tab))) for x in ids})
    pairs = [(u, c[0]) for c in cosets for u in c[1:]]
    classes = set()
    for g in ids:
        orb = {tab[tab[x][g]][inv[x]] for x in ids}
        classes.add(tuple(sorted(orb | {inv[y] for y in orb})))
    classes = sorted(classes)
    seen = set()
    for mask in range(1 << len(classes)):
        support = set().union(*(set(c) for i, c in enumerate(classes)
                                 if (mask >> i) & 1))
        def f(u, v):
            return int(tab[inv[u]][v] in support)
        neg_gram = [[-f(u,v)+f(u,b)+f(a,v)-f(a,b) for v,b in pairs]
                    for u,a in pairs]
        actual = positive_definite(neg_gram)
        enlarged = support | {0}
        predicted = (0 not in support and H <= enlarged and
                     all(enlarged.isdisjoint(c) or set(c) <= enlarged for c in cosets))
        assert actual == predicted, (name, support, actual, predicted)
        if actual:
            seen.add(tuple(sorted(support)))
    minimum = min(map(len, seen))
    assert minimum == len(H) - 1
    return name, len(ids), len(H), 1 << len(classes), len(seen), minimum

if __name__ == "__main__":
    print("group   |G| |[G,G]| candidates qualifying min-support")
    for name in ["S3xC2", "A4", "S4"]:
        print(*check(name))
