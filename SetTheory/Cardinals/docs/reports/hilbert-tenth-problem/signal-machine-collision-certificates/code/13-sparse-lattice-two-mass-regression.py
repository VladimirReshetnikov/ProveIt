#!/usr/bin/env python3
"""Deterministic checks of the far-encounter lemma on reversible NC-PCAs.

This is a finite regression test, not a substitute for the proof.
Every sampled rule is a mass-layer permutation on a three-part radius-1 PCA.
Only layers of mass <=2 can arise in the tested configurations.
"""
from itertools import product
from random import Random

RNG = Random(20261002)
ZERO = (0, 0, 0)
LAYERS = {m: [q for q in product(range(3), repeat=3) if sum(q) == m]
          for m in range(3)}
Q1 = LAYERS[1]

def rule():
    g = {}
    for layer in LAYERS.values():
        targets = layer[:]
        RNG.shuffle(targets)
        g.update(zip(layer, targets))
    return g

def step(g, c):
    out = {}
    for i in {j + k for j in c for k in (-1, 0, 1)}:
        inp = (c.get(i-1, ZERO)[2], c.get(i, ZERO)[1], c.get(i+1, ZERO)[0])
        q = g[inp]
        if q != ZERO:
            out[i] = q
    assert sum(map(sum, out.values())) == sum(map(sum, c.values()))
    return out

def walkers(g):
    alpha, disp = {}, {}
    for a in Q1:
        c = step(g, {0: a})
        assert len(c) == 1
        (v, b), = c.items()
        assert b in Q1 and -1 <= v <= 1
        alpha[a], disp[a] = b, v
    return alpha, disp

def accelerated(g, left, right, a, b):
    assert right-left > 2
    alpha, disp = walkers(g)
    seen, records = {}, []
    q, u, v, t = (a, b), left, right, 0
    while q not in seen:
        seen[q] = t
        records.append((u, v, *q))
        u, v = u+disp[q[0]], v+disp[q[1]]
        q = (alpha[q[0]], alpha[q[1]])
        t += 1
    mu, period = seen[q], t-seen[q]
    dl, dr = u-records[mu][0], v-records[mu][1]
    candidates = [i for i in range(mu) if records[i][1]-records[i][0] <= 2]
    for s in range(period):
        h = records[mu+s][1]-records[mu+s][0]
        drift = dr-dl
        if h <= 2:
            k = 0
        elif drift < 0:
            k = (h-2 + (-drift)-1)//(-drift)
        else:
            continue
        candidates.append(mu+s+k*period)
    first = min(candidates) if candidates else None
    def configuration(t):
        if t < mu:
            u, v, a, b = records[t]
        else:
            k, s = divmod(t-mu, period)
            u, v, a, b = records[mu+s]
            u, v = u+k*dl, v+k*dr
        assert u != v
        return {u: a, v: b}
    return first, configuration

def main():
    cases = 0
    for _ in range(150):
        g = rule()
        for a, b in product(Q1, repeat=2):
            for gap in (3, 4, 7, 31, 101):
                left = RNG.randrange(-30, 31)
                first, predicted = accelerated(g, left, left+gap, a, b)
                c = {left: a, left+gap: b}
                limit = first if first is not None else 450
                for t in range(limit+1):
                    assert c == predicted(t), (t, first, c, predicted(t))
                    assert (max(c)-min(c) <= 2) == (t == first)
                    if t != limit:
                        c = step(g, c)
                cases += 1
        # Splitting and merging remain in the explicitly enumerated near layer.
        for a in LAYERS[2]:
            c = step(g, {0: a})
            assert max(c)-min(c) <= 2
        for gap in (1, 2):
            for a, b in product(Q1, repeat=2):
                c = step(g, {0: a, gap: b})
                assert max(c)-min(c) <= 4
    # The huge input tests binary arithmetic, without a linear-time walk.
    g = {q:q for layer in LAYERS.values() for q in layer}
    alpha, disp = walkers(g)
    # Different mass-layer permutations allow a simple inward pair.
    g.update({(1,0,0):(0,0,1), (0,1,0):(0,1,0), (0,0,1):(1,0,0)})
    first, pred = accelerated(g, -(10**100), 10**100, (0,0,1), (1,0,0))
    assert first == 10**100-1
    assert max(pred(first))-min(pred(first)) == 2
    print(f'PASS: {cases} sampled far segments; near splitting/merging bounds; 100-digit encounter time')

if __name__ == '__main__':
    main()
