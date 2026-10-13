"""Independent input construction and crossing-cube rank oracle."""
from __future__ import annotations
from collections import defaultdict
from fastunknot.scan_fast import FastScan


def braid_pd(strands: int, word: list[int]):
    if type(strands) is not int or strands < 2 or not word:
        raise ValueError('use a nonempty braid on at least two strands')
    if any(type(x) is not int or x == 0 or abs(x) >= strands for x in word):
        raise ValueError('invalid braid generator')
    top = list(range(strands))
    current = top[:]
    pd, next_label = [], strands
    touched = set()
    for gen in word:
        j = abs(gen) - 1
        touched.update((j, j + 1))
        tl, tr = current[j:j + 2]
        bl, br = next_label, next_label + 1
        next_label += 2
        crossing = (tl, bl, br, tr)
        if gen < 0:
            crossing = crossing[1:] + crossing[:1]
        pd.append(crossing)
        current[j:j + 2] = [bl, br]
    if len(touched) != strands:
        raise ValueError('untouched braid strand would be an implicit circle')
    parent = list(range(next_label))
    def root(a):
        while parent[a] != a:
            a = parent[a]
        return a
    for a, b in zip(current, top):
        parent[root(a)] = root(b)
    pd = [tuple(root(a) for a in c) for c in pd]
    return pd


def circles(pd, mask):
    labels = sorted({a for c in pd for a in c})
    parent = {a: a for a in labels}
    def root(a):
        while parent[a] != a:
            a = parent[a]
        return a
    for i, (a, b, c, d) in enumerate(pd):
        smoothing = ((a, d), (b, c)) if mask >> i & 1 else ((a, b), (c, d))
        for x, y in smoothing:
            parent[root(x)] = root(y)
    groups = defaultdict(set)
    for a in labels:
        groups[root(a)].add(a)
    components = sorted((frozenset(g) for g in groups.values()), key=min)
    owner = {a: j for j, comp in enumerate(components) for a in comp}
    return components, owner


def cube_ranks(pd, max_crossings=10):
    """F2 Frobenius cube, without Planar/scan algebra or cancellations."""
    n = len(pd)
    if n > max_crossings:
        raise ValueError('cube oracle crossing ceiling')
    states = [circles(pd, s) for s in range(1 << n)]
    objects, index = defaultdict(list), {}
    for s, (comps, _) in enumerate(states):
        h = s.bit_count()
        for dots in range(1 << len(comps)):
            index[s, dots] = len(objects[h])
            objects[h].append((s, dots))
    rank = defaultdict(int)
    for h, sources in objects.items():
        pivots = {}
        for s, dots in sources:
            old, own = states[s]
            column = 0
            for cross in range(n):
                if s >> cross & 1:
                    continue
                t = s | (1 << cross)
                new, new_own = states[t]
                affected_old = {own[a] for a in pd[cross]}
                affected_new = {new_own[a] for a in pd[cross]}
                base = 0
                for k, comp in enumerate(old):
                    if k not in affected_old and dots >> k & 1:
                        base |= 1 << new_own[next(iter(comp))]
                outputs = []
                if len(new) == len(old) - 1:
                    if len(affected_old) != 2 or len(affected_new) != 1:
                        raise ArithmeticError('unexpected merge')
                    count = sum(dots >> k & 1 for k in affected_old)
                    if count < 2:
                        outputs = [base | ((1 << next(iter(affected_new))) if count else 0)]
                elif len(new) == len(old) + 1:
                    if len(affected_old) != 1 or len(affected_new) != 2:
                        raise ArithmeticError('unexpected split')
                    x, y = sorted(affected_new)
                    if dots >> next(iter(affected_old)) & 1:
                        outputs = [base | (1 << x) | (1 << y)]
                    else:
                        outputs = [base | (1 << x), base | (1 << y)]
                else:
                    raise ArithmeticError('classical smoothing must merge or split')
                for value in outputs:
                    column ^= 1 << index[t, value]
            while column:
                top = column.bit_length() - 1
                if top not in pivots:
                    pivots[top] = column
                    break
                column ^= pivots[top]
        rank[h] = len(pivots)
    return {h: len(v) - rank[h - 1] - rank[h] for h, v in sorted(objects.items())
            if len(v) - rank[h - 1] - rank[h]}


def scan_pd(pd, cls=FastScan, *, order=None, check=False, **kwargs):
    scan = cls(shape_cache=False, **kwargs)
    for index in (range(len(pd)) if order is None else order):
        scan.add_crossing(pd[index])
        if check:
            scan.check_d_squared()
    return scan


def profile(scan):
    result = defaultdict(int)
    for j, m in enumerate(scan.mid):
        if m is not None:
            result[scan.deg[j], scan.algebra.pairs[m]] += 1
    return dict(result)


def open_edge(pd):
    """Cut one diagram edge, producing a long-knot (two-point) tangle."""
    result = list(pd)
    label = result[0][0]
    fresh = max(a for c in pd for a in c) + 1
    row = list(result[0])
    row[0] = fresh
    result[0] = tuple(row)
    return result, (label, fresh)


def concatenate_tangles(tangles):
    """Join output endpoint to input endpoint, renumbering disjoint copies."""
    result, next_label, first, last = [], 0, None, None
    for pd, (a, b) in tangles:
        mapping = {}
        for label in sorted({x for c in pd for x in c}):
            mapping[label] = next_label
            next_label += 1
        if last is not None:
            mapping[a] = last
        else:
            first = mapping[a]
        last = mapping[b]
        result.extend(tuple(mapping[x] for x in c) for c in pd)
    return result, (first, last)

import random
from fastunknot.planar import Planar
from fastunknot.radical_transfer import Complex, bits

def block_problem(b, m, q, seed=427, sparse=False, scalar_mix=False):
    rng=random.Random(seed)
    alg=Planar(False)
    matching=alg.intern(tuple((2*j,2*j+1) for j in range(b)))
    size=m+q
    out=[{} for _ in range(2*size)]
    # Top-left constant matrix is invertible. Other constant blocks vanish.
    const=[1<<j for j in range(m)]
    if scalar_mix:
        for _ in range(6*m):
            a,c=rng.sample(range(m),2)
            const[a]^=const[c]
    for j in range(size):
        for k in range(size):
            if sparse and j!=k: continue
            value=rng.getrandbits(1<<b) & ~1
            if j<m and k<m and (const[j]>>k)&1: value|=1
            if value: out[j][size+k]=value
    return alg,Complex([matching]*(2*size),[0]*size+[1]*size,out)


def regular_representation_homology(c,alg):
    """Independent F2 expansion of a two-term square-free-ring complex."""
    if not c.mid:return (0,0)
    if len(set(c.mid))!=1 or set(c.deg)-{0,1}:raise ValueError('requires one-matching two-term complex')
    b=len(alg.pairs[c.mid[0]]);dim=1<<b
    sources=[j for j,h in enumerate(c.deg) if h==0]
    targets={j:k for k,j in enumerate(j for j,h in enumerate(c.deg) if h==1)}
    pivots={}
    for j in sources:
        for S in range(dim):
            col=0
            for k,f in c.out[j].items():
                for T in bits(f):
                    if not S&T:col^=1<<(targets[k]*dim+(S|T))
            while col:
                top=col.bit_length()-1
                if top not in pivots:pivots[top]=col;break
                col^=pivots[top]
    rank=len(pivots)
    return (len(sources)*dim-rank,len(targets)*dim-rank)

