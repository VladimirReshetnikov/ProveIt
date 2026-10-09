"""Independent literal free-group and Whitehead oracles, for small tests only."""
from itertools import combinations
from functools import lru_cache


def inverse(word):
    return tuple(-x for x in reversed(word))


def freely_reduce(word):
    out = []
    for x in word:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def cyclic_reduce(word):
    w = freely_reduce(word)
    i, j = 0, len(w)
    while i < j and w[i] == -w[j-1]:
        i += 1; j -= 1
    return w[i:j]


def whitehead_images(a, subset):
    """The four-case type-II definition, not a cut-graph length formula."""
    images = {}
    for x in (1, -1, 2, -2):
        if abs(x) == abs(a):
            images[x] = (x,)
        else:
            left, right = -x in subset, x in subset
            if left and right: images[x] = (-a, x, a)
            elif left: images[x] = (-a, x)
            elif right: images[x] = (x, a)
            else: images[x] = (x,)
    return images


WHITEHEAD = []
for _a in (1, -1, 2, -2):
    _others = [x for x in (1, -1, 2, -2) if abs(x) != abs(_a)]
    for _mask in range(4):
        _A = {_a} | {x for k, x in enumerate(_others) if _mask >> k & 1}
        WHITEHEAD.append(whitehead_images(_a, _A))


def whitehead_primitive(word):
    """Whitehead's strict descent theorem decides primitivity at small length."""
    w = cyclic_reduce(word)
    while len(w) > 1:
        best = w
        for images in WHITEHEAD:
            candidate = cyclic_reduce(y for x in w for y in images[x])
            if len(candidate) < len(best): best = candidate
        if len(best) == len(w): return False
        w = best
    return len(w) == 1


def literal_root(word):
    w = tuple(word)
    if not w: return (), 0
    # KMP prefix function: no slope or height information is used.
    pi = [0]*len(w)
    for i in range(1, len(w)):
        j = pi[i-1]
        while j and w[j] != w[i]: j = pi[j-1]
        if w[j] == w[i]: j += 1
        pi[i] = j
    p = len(w)-pi[-1]
    return (w[:p], len(w)//p) if len(w) % p == 0 else (w, 1)


def whitehead_primitive_power(word):
    w = cyclic_reduce(word)
    root, d = literal_root(w)
    return whitehead_primitive(root), d


def literal_width(word):
    from math import gcd
    w = tuple(word)
    if not w: return None
    a = sum(x == 1 for x in w); A = sum(x == -1 for x in w)
    b = sum(x == 2 for x in w); B = sum(x == -2 for x in w)
    if a*A or b*B: return None
    u, v = a-A, b-B
    d = gcd(abs(u), abs(v)); u //= d; v //= d
    lo = hi = current = 0
    for x in w:
        current += v if x == 1 else -v if x == -1 else -u if x == 2 else u
        lo = min(lo, current); hi = max(hi, current)
    return hi-lo, abs(u)+abs(v)-1, d
