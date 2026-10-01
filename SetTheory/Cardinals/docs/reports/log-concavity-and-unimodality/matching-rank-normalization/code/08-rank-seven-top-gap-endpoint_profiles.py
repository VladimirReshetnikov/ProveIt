"""Exact endpoint-set profile counting, with repeated neighborhood classes."""
from itertools import combinations, combinations_with_replacement
from functools import lru_cache
from math import comb
from collections import Counter
@lru_cache(None)
def endpoints(cols):
    states = {0}
    for c in cols:
        states = {I | bit for I in states for bit in bits(c & ~I)}
    return tuple(sorted(states))

def bits(x):
    while x:
        b = x & -x
        x -= b
        yield b

def left_signatures(left, b):
    out = [{} for j in range(b + 1)]
    counts = Counter(left)
    for j in range(b + 1):
        for J in combinations_with_replacement(sorted(counts), j):
            wt = 1
            for typ, m in Counter(J).items():
                wt *= comb(counts[typ], m) if counts[typ] >= m else 0
            if not wt:
                continue
            sig = endpoints(J)
            if sig:
                out[j][sig] = out[j].get(sig, 0) + wt
    return out

def coefficient_profiles(core, left, a, b, types=None):
    ls = left_signatures(tuple(left), b)
    bcols = [sum((1 << i for i, row in enumerate(core) if row >> j & 1)) for j in range(b)]
    out = []
    for j in range(a + 1):
        entries = []
        for R in combinations_with_replacement(range(1, 1 << a) if types is None else types, j):
            total = 0
            for sz in range(a + 1):
                ell = b + j - sz
                if not 0 <= ell <= b:
                    continue
                for I in combinations(range(a), sz):
                    mask = sum((1 << i for i in I))
                    good = set()
                    for BJ in combinations(range(b), ell):
                        bm = sum((1 << i for i in BJ))
                        cols = tuple(sorted([bcols[z] & mask for z in range(b) if not bm >> z & 1] + [r & mask for r in R]))
                        if mask in endpoints(cols):
                            good.add(bm)
                    total += sum((n for sig, n in ls[ell].items() if any((x in good for x in sig))))
            if total:
                entries.append((R, total))
        out.append(entries)
    return out
