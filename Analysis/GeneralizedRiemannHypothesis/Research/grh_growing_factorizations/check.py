#!/usr/bin/env python3
"""Finite checks accompanying paper.tex. No analytic or Lean verification claimed.

Type groups are products of cyclic groups. All tests use exact integers.
Run: python3 check.py
"""
from collections import Counter
from itertools import product
from math import factorial, lcm, prod
from random import Random


def types(moduli):
    return list(product(*(range(n) for n in moduli)))


def add(x, y, moduli):
    return tuple((a+b) % n for a,b,n in zip(x,y,moduli))


def signature(table, moduli):
    ts = types(moduli)
    r = len(table[0])
    return tuple(tuple(sum(table[i][j]*ts[i][h] for i in range(len(ts))) % n
                       for h,n in enumerate(moduli)) for j in range(r))


def margins(table):
    return tuple(map(sum,table)), tuple(map(sum,zip(*table)))


def table_distance(a,b):
    return sum(max(x-y,0) for ar,br in zip(a,b) for x,y in zip(ar,br))


def repair(a, b, moduli):
    """Return C and cycle statistics as in Lemma 5.1.

    Vertex 0..D-1 is a type; D..D+r-1 is a label.
    Every cycle increment is sign-compatible with b-a. Reduce coefficients mod e.
    """
    D, r = len(a), len(a[0])
    assert D == prod(moduli) and margins(a) == margins(b)
    e = lcm(*moduli)
    arcs = {}
    for t in range(D):
        for j in range(r):
            z = b[t][j]-a[t][j]
            if z > 0: arcs[t,D+j] = z
            if z < 0: arcs[D+j,t] = -z
    c = [row[:] for row in a]
    initial_arcs = len(arcs)
    ncycles = 0
    maxlen = 0
    while arcs:
        adj = {}
        for u,v in arcs:
            adj.setdefault(u,[]).append(v)
        u = next(iter(adj))
        visited = {}
        path = []
        while u not in visited:
            visited[u] = len(path)
            path.append(u)
            assert u in adj, 'balanced residual flow cannot have a dead end'
            u = adj[u][0]
        cyc = path[visited[u]:] + [u]
        edges = list(zip(cyc,cyc[1:]))
        assert len(edges) % 2 == 0 and len(edges) <= 2*D
        weight = min(arcs[edge] for edge in edges)
        reduced = weight % e
        for edge in edges:
            u,v = edge
            if u < D:
                assert v >= D
                c[u][v-D] += reduced
            else:
                assert v < D
                c[v][u-D] -= reduced
            arcs[edge] -= weight
            if arcs[edge] == 0: del arcs[edge]
        ncycles += 1
        maxlen = max(maxlen,len(edges))
    assert ncycles <= initial_arcs <= D*r
    assert margins(c) == margins(a)
    assert all(min(x,y) <= z <= max(x,y) and (z-y)%e == 0
               for ar,br,cr in zip(a,b,c) for x,y,z in zip(ar,br,cr))
    assert signature(c,moduli) == signature(b,moduli)
    distance = table_distance(a,c)
    assert distance <= D*D*(e-1)*r
    assert distance <= table_distance(a,b)
    return c, distance, ncycles, maxlen


def counts(objects, labels, moduli, r):
    idx = {t:i for i,t in enumerate(types(moduli))}
    a = [[0]*r for _ in idx]
    for t,j in zip(objects,labels): a[idx[t]][j] += 1
    return a


def dp(objects, quotas, moduli):
    """Compressed DP, tracking first r-1 counts and type products only."""
    r = len(quotas)
    zero = (0,)*len(moduli)
    start = ((0,)*(r-1), (zero,)*(r-1))
    state = Counter({start:1})
    peak = 1
    for i,t in enumerate(objects):
        nxt = Counter()
        for (ks, sig), ways in state.items():
            if i-sum(ks) < quotas[-1]:
                nxt[ks,sig] += ways
            for j in range(r-1):
                if ks[j] >= quotas[j]: continue
                kk = list(ks); kk[j] += 1
                ss = list(sig); ss[j] = add(ss[j],t,moduli)
                nxt[tuple(kk),tuple(ss)] += ways
        state = nxt
        peak = max(peak,len(state))
    total = tuple(sum(t[h] for t in objects)%n for h,n in enumerate(moduli))
    out = Counter()
    for (ks,sig), ways in state.items():
        assert ks == tuple(quotas[:-1])
        last = tuple((total[h]-sum(s[h] for s in sig))%n for h,n in enumerate(moduli))
        out[sig+(last,)] += ways
    assert peak <= prod(moduli)**(r-1)*prod(k+1 for k in quotas[:-1])
    assert sum(out.values()) == factorial(len(objects))//prod(factorial(k) for k in quotas)
    return out,peak


def brute(objects, quotas, moduli):
    r = len(quotas)
    out = Counter()
    remaining = list(quotas)
    zero = (0,)*len(moduli)
    sig = [zero]*r
    def rec(i):
        if i == len(objects):
            out[tuple(sig)] += 1
            return
        for j in range(r):
            if not remaining[j]: continue
            remaining[j] -= 1
            old = sig[j]
            sig[j] = add(old,objects[i],moduli)
            rec(i+1)
            sig[j] = old
            remaining[j] += 1
    rec(0)
    return out


def test_repair():
    rng = Random(20261127)
    trials = 0
    max_repaired = 0
    max_original = 0
    for mods in [(1,), (2,), (3,), (4,), (2,2), (2,3), (2,2,2)]:
        ts = types(mods)
        for r in [2,3,5,12,30,80]:
            for rep in range(12):
                m = r*rng.randint(1,80)
                obj = rng.choices(ts,k=m)
                x = [j for j in range(r) for _ in range(m//r)]
                y = x[:]; rng.shuffle(x); rng.shuffle(y)
                a,b = counts(obj,x,mods,r),counts(obj,y,mods,r)
                c,dist,ncycles,maxlen = repair(a,b,mods)
                max_repaired = max(max_repaired,dist)
                max_original = max(max_original,table_distance(a,b))
                trials += 1
    # The quotient repair can be zero even for a huge change in allocations.
    a = [[300001,0,0],[0,300001,0],[0,0,300001]]
    b = [[0,300001,0],[0,0,300001],[300001,0,0]]
    c,dist,ncycles,maxlen = repair(a,b,(3,))
    assert dist == 3 and table_distance(a,b) == 900003 and ncycles == 1
    print(f'Random table repair checks: {trials}; largest observed original distance {max_original}; largest repaired distance {max_repaired}')
    print(f'Large cycle fixture: {table_distance(a,b)} original moves -> {dist} repaired moves; cycle length {maxlen}')


def test_dp():
    rng = Random(20261128)
    trials = 0
    allocations = 0
    peak = 0
    for mods in [(1,), (2,), (3,), (2,2), (2,3)]:
        for _ in range(15):
            m = rng.randint(4,10)
            r = rng.randint(2,min(4,m))
            cuts = [0] + sorted(rng.sample(range(1,m),r-1)) + [m]
            q = [b-a for a,b in zip(cuts,cuts[1:])]
            obj = rng.choices(types(mods),k=m)
            out,p = dp(obj,q,mods)
            assert out == brute(obj,q,mods)
            trials += 1
            allocations += sum(out.values())
            peak = max(peak,p)
    print(f'Exact DP vs exhaustive enumeration: {trials} instances; {allocations} assignments total; peak state count {peak}')


def prime_example():
    # Eight quadratic residues and one nonresidue mod 7. The exact type
    # masses depend on quotas, not just on the total-product constraint.
    ps = [11,23,29,37,43,53,71,79,3]
    qs = (1,2,3,3)
    obj = [(0 if pow(p,3,7)==1 else 1,) for p in ps]
    assert sum(x[0] for x in obj)==1
    out,peak = dp(obj,qs,(2,))
    total = sum(out.values())
    assert out == brute(obj,qs,(2,))
    assert len(out)==4
    print(f'Mod-7 example: primes={ps}, quotas={qs}, total allocations={total}, peak states={peak}')
    for sig,count in sorted(out.items()):
        j = next(i for i,x in enumerate(sig) if x==(1,))
        assert count*len(ps) == qs[j]*total
        print('  signs', ''.join('+' if t==(0,) else '-' for t in sig), f'count={count}, mass={qs[j]}/{len(ps)}')
    print('  Only four of eight compatible sign patterns occur. No asymptotic claim is made for this finite example.')


if __name__ == '__main__':
    test_repair()
    test_dp()
    prime_example()
    print('All finite checks passed.')
