"""Validated classical PD codes and exact matching splicing.
Slots are cyclic; 0 is opposite 2, and 1 is opposite 3. The empty PD denotes
one crossingless unknot, never an unspecified collection of circles.
"""
from __future__ import annotations
from collections import Counter

class DSU:
    def __init__(self, values): self.parent = {v: v for v in values}
    def find(self, a):
        p = self.parent
        while p[a] != a:
            p[a] = p[p[a]]
            a = p[a]
        return a
    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b: self.parent[max(a,b)] = min(a,b)

def cycles(perm):
    seen, count = set(), 0
    for start in range(len(perm)):
        if start in seen: continue
        count += 1
        j = start
        while j not in seen:
            seen.add(j); j = perm[j]
    return count

def canonical(pd):
    labels = sorted({x for c in pd for x in c})
    mp = {x: j for j, x in enumerate(labels)}
    return [tuple(mp[x] for x in c) for c in pd]

def component_count(pd):
    if not pd: return 1
    labels = {x for c in pd for x in c}
    ds = DSU(labels)
    for a, b, c, d in pd:
        ds.union(a,c); ds.union(b,d)
    return len({ds.find(x) for x in labels})

def validate(pd, *, knot=False):
    if not isinstance(pd, (list, tuple)): raise ValueError('PD must be a sequence')
    pd = [tuple(c) for c in pd]
    if any(len(c) != 4 or any(type(x) is not int or x < 0 for x in c) for c in pd):
        raise ValueError('PD crossings require four nonnegative integer labels')
    if not pd: return pd
    occ = {}
    for i, c in enumerate(pd):
        for j, x in enumerate(c): occ.setdefault(x, []).append(4*i+j)
    if any(len(v) != 2 for v in occ.values()): raise ValueError('each edge must occur exactly twice')
    n = len(pd); alpha = [0]*(4*n)
    ds = DSU(range(n))
    for a, b in occ.values():
        alpha[a] = b; alpha[b] = a; ds.union(a//4,b//4)
    projection_components = len({ds.find(i) for i in range(n)})
    # Face permutation sigma o alpha for the given oriented ribbon embedding.
    faces = cycles([4*(alpha[j]//4)+(alpha[j]+1)%4 for j in range(4*n)])
    if n - 2*n + faces != 2*projection_components:
        raise ValueError('PD rotation system is not planar (virtual inputs unsupported)')
    if knot and component_count(pd) != 1: raise ValueError('recognition requires one knot component')
    return pd

def braid_pd(strands: int, word):
    word = list(word)
    if type(strands) is not int or strands < 2 or not word:
        raise ValueError('use a nonempty braid on at least two strands')
    if any(type(x) is not int or not 0 < abs(x) < strands for x in word):
        raise ValueError('invalid generator')
    top = list(range(strands)); current = top[:]
    rows, nxt, touched = [], strands, set()
    for gen in word:
        j = abs(gen)-1; touched.update((j,j+1))
        tl,tr = current[j:j+2]; bl,br = nxt,nxt+1; nxt += 2
        c = (tl,bl,br,tr)
        rows.append(c if gen > 0 else c[1:]+c[:1])
        current[j:j+2] = [bl,br]
    if len(touched) != strands: raise ValueError('implicit crossingless braid component unsupported')
    ds = DSU(range(nxt))
    for a,b in zip(current,top): ds.union(a,b)
    return validate(canonical([tuple(ds.find(x) for x in c) for c in rows]))

def splice(suffix, pairs):
    """Close suffix by a geometrically certified frontier matching.
    PD validation is a defense against malformed matchings, not a replacement
    for the scanner provenance that establishes this is a true direct summand.
    """
    suffix = [tuple(c) for c in suffix]; pairs = [tuple(p) for p in pairs]
    counts = Counter(x for c in suffix for x in c)
    frontier = {x for x,v in counts.items() if v == 1}
    ends = [x for p in pairs for x in p]
    if any(len(p) != 2 or p[0] == p[1] for p in pairs): raise ValueError('invalid matching arc')
    if len(ends) != len(set(ends)) or set(ends) != frontier:
        raise ValueError('matching must cover exactly the suffix frontier')
    if any(v not in (1,2) for v in counts.values()): raise ValueError('invalid suffix edge counts')
    if not suffix: raise ValueError('empty-boundary final stages use scalar homology, not splicing')
    ds = DSU(counts)
    for a,b in pairs: ds.union(a,b)
    return validate(canonical([tuple(ds.find(x) for x in c) for c in suffix]))
