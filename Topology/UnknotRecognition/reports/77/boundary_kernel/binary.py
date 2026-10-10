"""Independent binary Magnus and two-sheet cellular-chain reference kernels."""
from __future__ import annotations
from .kernel import SLP, exponent_mod


def parity(x: int) -> int: return x.bit_count() & 1


def symplectic(x: int, y: int, g: int) -> int:
    out = 0
    for i in range(g):
        out ^= ((x >> (2*i)) & 1) & ((y >> (2*i+1)) & 1)
        out ^= ((x >> (2*i+1)) & 1) & ((y >> (2*i)) & 1)
    return out


def j_action(x: int, g: int) -> int:
    return sum(((x >> (j ^ 1)) & 1) << j for j in range(2*g))


def rank(rows) -> int:
    pivots = {}
    for x in rows:
        while x:
            p = x.bit_length()-1
            if p in pivots: x ^= pivots[p]
            else:
                pivots[p] = x
                break
    return len(pivots)


def magnus(slp: SLP, g: int):
    d = 2*g
    zero = (0, (0,)*d)
    def mul(a, b):
        x,m = a; y,n = b
        return x ^ y, tuple(m[j] ^ n[j] ^ (y if (x >> j) & 1 else 0) for j in range(d))
    def inv(a):
        x,m = a
        return x, tuple(m[j] ^ (x if (x >> j) & 1 else 0) for j in range(d))
    values = []
    for r in slp.rules:
        if r[0] == 'id': value = zero
        elif r[0] == 'gen':
            j = abs(r[1])-1
            if j >= d: raise ValueError('letter outside surface')
            x = 1 << j
            value = (x, tuple(x if i == j and r[1] < 0 else 0 for i in range(d)))
        elif r[0] == 'cat': value = mul(values[r[1]],values[r[2]])
        elif r[0] == 'inv': value = inv(values[r[1]])
        else:
            value = zero
            for _ in range(exponent_mod(r[2],4)): value = mul(value,values[r[1]])
        values.append(value)
    return values[slp.root]


def contraction(rows, alpha: int) -> int:
    out = 0
    for j, row in enumerate(rows):
        if (alpha >> j) & 1: out ^= row
    return out


def doubled_chain(x: int, d: int) -> int:
    return sum((3 << (2*j)) for j in range(d) if (x >> j) & 1)


def lift_chain(slp: SLP, g: int, alpha: int):
    """Monodromy and mod-2 edge chains from the two possible starting sheets."""
    if not 0 < alpha < 1 << (2*g): raise ValueError('nonzero character required')
    def mul(a, b):
        e,c0,c1 = a; f,d0,d1 = b
        return e ^ f, c0 ^ (d1 if e else d0), c1 ^ (d0 if e else d1)
    values = []
    for r in slp.rules:
        if r[0] == 'id': value = (0,0,0)
        elif r[0] == 'gen':
            j = abs(r[1])-1
            if j >= 2*g: raise ValueError('letter outside surface')
            e = (alpha >> j) & 1
            start = e if r[1] < 0 else 0
            value = (e, 1 << (2*j+start), 1 << (2*j+(start^1)))
        elif r[0] == 'cat': value = mul(values[r[1]],values[r[2]])
        elif r[0] == 'inv':
            e,c0,c1 = values[r[1]]
            value = (e,c1,c0) if e else (e,c0,c1)
        else:
            value = (0,0,0)
            for _ in range(exponent_mod(r[2],4)): value = mul(value,values[r[1]])
        values.append(value)
    return values[slp.root]


def optimal_characters(g: int):
    if g < 2: return []
    basis = [1 << (2*i) for i in range(g)]
    return basis + [sum(basis)]


def cover_observation(slp: SLP, g: int):
    x, rows = magnus(slp,g)
    if x: return {'base_homology_nonzero':True, 'detected_by':[]}
    hits = []
    for alpha in optimal_characters(g):
        if contraction(rows,alpha) not in (0,j_action(alpha,g)): hits.append(alpha)
    return {'base_homology_nonzero':False, 'detected_by':hits}
