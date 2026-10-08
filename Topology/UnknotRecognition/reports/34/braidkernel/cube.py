"""Small-instance independent reduced Khovanov oracle over F_2.

This is a complete exponential backend with caps disabled, not a fast scanner.
The marked circle is labelled x in F_2[x]/(x^2). No quantum grading is output.
"""
from __future__ import annotations
from dataclasses import dataclass
from time import monotonic
from .core import Braid

class ResourceLimit(RuntimeError):
    pass

class DSU:
    def __init__(self, n: int):
        self.p = list(range(n))
        self.s = [1]*n
    def find(self, a: int) -> int:
        while a != self.p[a]:
            self.p[a] = self.p[self.p[a]]
            a = self.p[a]
        return a
    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a == b:
            return
        if self.s[a] < self.s[b]:
            a, b = b, a
        self.p[b] = a
        self.s[a] += self.s[b]


def resolution(braid: Braid, state: int) -> tuple[frozenset[int], ...]:
    n, b = len(braid.word), braid.strands
    dsu, top = DSU(b+2*n), list(range(b))
    for j, g in enumerate(braid.word):
        i = abs(g)-1
        a, z = top[i], top[i+1]
        c, d = b+2*j, b+2*j+1
        horizontal = bool((state >> j) & 1) == (g > 0)
        if horizontal:
            dsu.union(a, z)
            dsu.union(c, d)
        else:
            dsu.union(a, c)
            dsu.union(z, d)
        top[i], top[i+1] = c, d
    for i in range(b):
        dsu.union(i, top[i])
    components: dict[int, set[int]] = {}
    for i in range(b+2*n):
        components.setdefault(dsu.find(i), set()).add(i)
    return tuple(sorted((frozenset(s) for s in components.values()), key=min))


def edge_labels(source, target, label: int):
    """Frobenius multiplication/comultiplication, with x encoded by bit 1."""
    lookup = {s:j for j,s in enumerate(target)}
    common = [(i, lookup[s]) for i,s in enumerate(source) if s in lookup]
    common_s, common_t = {i for i,j in common}, {j for i,j in common}
    changed_s = [i for i in range(len(source)) if i not in common_s]
    changed_t = [j for j in range(len(target)) if j not in common_t]
    out = sum(((label >> i) & 1) << j for i,j in common)
    if len(changed_s) == 2 and len(changed_t) == 1:
        a, b = ((label >> i) & 1 for i in changed_s)
        if a and b:
            return ()
        answer = out | ((a | b) << changed_t[0])
        return (answer,) if answer & 1 else ()
    if len(changed_s) == 1 and len(changed_t) == 2:
        a = (label >> changed_s[0]) & 1
        u, v = changed_t
        answers = (out | (1 << u) | (1 << v),) if a else (out | (1 << u), out | (1 << v))
        return tuple(x for x in answers if x & 1)
    raise ArithmeticError('edge is not an ordinary merge/split')


def gf2_rank(columns: list[int]) -> int:
    pivots: dict[int, int] = {}
    for v in columns:
        while v:
            p = v.bit_length()-1
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)


def reduced_khovanov(braid: Braid, *, max_crossings: int | None = 12,
                     max_generators: int | None = 200000, seconds: float | None = None,
                     check_d_squared: bool = False) -> dict:
    braid = Braid.checked(braid.strands, braid.word)
    n = len(braid.word)
    if max_crossings is not None and n > max_crossings:
        raise ResourceLimit('crossing cap exceeded')
    start = monotonic()
    def check():
        if seconds is not None and monotonic()-start >= seconds:
            raise ResourceLimit('time budget exceeded')
    circles, offsets, dimensions = [], [], [0]*(n+1)
    total = 0
    for state in range(1 << n):
        check()
        cs = resolution(braid, state)
        circles.append(cs)
        h, size = state.bit_count(), 1 << (len(cs)-1)
        offsets.append(dimensions[h])
        dimensions[h] += size
        total += size
        if max_generators is not None and total > max_generators:
            raise ResourceLimit('enhanced-generator cap exceeded')
    matrices = [[0]*dimensions[h] for h in range(n)]
    for state, source in enumerate(circles):
        check()
        h = state.bit_count()
        if h == n:
            continue
        successors = [(state | (1 << j)) for j in range(n) if not (state >> j) & 1]
        for label in range(1, 1 << len(source), 2):
            col = 0
            for target_state in successors:
                for target_label in edge_labels(source, circles[target_state], label):
                    col ^= 1 << (offsets[target_state] + (target_label >> 1))
            matrices[h][offsets[state] + (label >> 1)] = col
    if check_d_squared:
        for h in range(n-1):
            check()
            for col in matrices[h]:
                composition = 0
                while col:
                    bit = col & -col
                    composition ^= matrices[h+1][bit.bit_length()-1]
                    col ^= bit
                if composition:
                    raise ArithmeticError('d squared is nonzero')
    ranks = []
    for matrix in matrices:
        check()
        ranks.append(gf2_rank(matrix))
    by_degree = [dimensions[h] - (ranks[h] if h < n else 0)
                 - (ranks[h-1] if h else 0) for h in range(n+1)]
    if any(x < 0 for x in by_degree):
        raise ArithmeticError('negative homology dimension')
    return {'reduced_rank': sum(by_degree), 'by_raw_degree': by_degree,
            'dimensions': dimensions, 'differential_ranks': ranks,
            'enhanced_generators': total, 'states': 1 << n,
            'd_squared_checked': check_d_squared,
            'seconds': monotonic()-start}


def normalized_bracket(braid: Braid) -> dict[int, int]:
    """Independent Laurent state sum, unknot normalized to 1 (variable A)."""
    from math import comb
    braid = Braid.checked(braid.strands, braid.word)
    n, w = len(braid.word), braid.exponent
    out: dict[int, int] = {}
    for state in range(1 << n):
        c = len(resolution(braid, state))-1
        base = n-2*state.bit_count()-3*w
        sign = -1 if (c+w) % 2 else 1
        for j in range(c+1):
            exponent = base+2*c-4*j
            out[exponent] = out.get(exponent, 0)+sign*comb(c,j)
    return {e:int(c) for e,c in out.items() if c}
