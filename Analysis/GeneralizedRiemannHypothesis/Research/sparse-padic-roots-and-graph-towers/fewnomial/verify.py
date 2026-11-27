"""Exact finite checks for the open-disk root theorems. Run with Python 3.9+."""
from fractions import Fraction
from math import comb, isqrt
from collections import Counter


def bound(p, t):
    h = (isqrt(8 * t + 1) - 1) // 2
    return (h - 1) * p + int(t - h * (h + 1) // 2 == h)


def partitions(n, limit=None):
    if n == 0:
        yield ()
        return
    for a in range(1, min(n, limit or n) + 1):
        for tail in partitions(n - a, a):
            yield (a,) + tail


def diagram_indices(p, multiplicities):
    diagonals = Counter()
    for b in range(max(multiplicities)):
        for i in range(sum(s > b for s in multiplicities)):
            diagonals[i + b] += 1
    return [d + (p - 1) * j for d in sorted(diagonals)
            for j in range(diagonals[d])]


def greedy_powers(p, slots, t):
    """Compute first independent residue jet columns without diagram formulas."""
    pivots = {}
    indices = []
    for d in range(t):
        for j in range(d + 1):
            k = d + (p - 1) * j
            col = [(comb(k, b) * pow(a, k - b, p)) % p if b <= k else 0
                   for a, s in slots for b in range(s)]
            for i in sorted(pivots):
                c = col[i]
                col = [(x - c * y) % p for x, y in zip(col, pivots[i])]
            pivot = next((i for i, x in enumerate(col) if x), None)
            if pivot is not None:
                inv = pow(col[pivot], -1, p)
                pivots[pivot] = [x * inv % p for x in col]
                indices.append(k)
    assert len(indices) == t
    return indices


def multiply(a, b):
    prod = Counter()
    for i, x in a.items():
        for j, y in b.items():
            prod[i + j] += x * y
    return {k: c for k, c in prod.items() if c}


def shifted(poly):
    """Taylor coefficients at 1 via the ordinary integer binomial theorem."""
    return [sum(v * comb(n, k) for n, v in poly.items() if k <= n)
            for k in range(max(poly) + 1)]


def val(n, p):
    if not n:
        raise ValueError("use only for nonzero coefficients")
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def disk_count(poly, p, radius, closed):
    vals = [(val(c, p) + radius * k, k)
            for k, c in enumerate(shifted(poly)) if c]
    best = min(w for w, k in vals)
    # A slight increase of radius breaks ties in favor of the least index.
    ties = [k for w, k in vals if w == best]
    return max(ties) if closed else min(ties)


def squarefree_mod(poly, q):
    """A squarefree reduction of a monic polynomial certifies separability over Q."""
    f = [poly.get(n, 0) % q for n in range(max(poly) + 1)]
    g = [(i * c) % q for i, c in enumerate(f)][1:]
    def trim(a):
        while a and not a[-1]:
            a.pop()
        return a
    g = trim(g)
    while g:
        while len(f) >= len(g):
            k, c = len(f) - len(g), (f[-1] * pow(g[-1], -1, q)) % q
            for i, a in enumerate(g):
                f[k + i] = (f[k + i] - c * a) % q
            trim(f)
        f, g = g, f
    return len(f) == 1


def product_witness(p, t):
    h = (isqrt(8 * t + 1) - 1) // 2
    e = t - h * (h + 1) // 2
    f = {1: 1, 0: -1} if e == h else {0: 1}
    for i in range(1, h):
        f = multiply(f, {p: 1, 1: -p, 0: p - 1 + i * p**3})
    return f


def jump_witness(p):
    f = Counter({j * p: comb(p, j) * (-1)**(p-j) for j in range(p+1)})
    f[p] -= p**p
    f[1] += p**(p+1)
    f[0] += p**p * (1-p) + p**(p+3)
    return {k: a for k, a in f.items() if a}


def main():
    profiles = residue_checks = products = 0
    for p in (2, 3, 5, 7, 11, 13, 17, 19):
        for t in range(1, p + 1):
            values = []
            for mult in partitions(t):
                predicted = diagram_indices(p, mult)
                values.append(max(predicted))
                profiles += 1
                if p <= 13:
                    for a, b in ((1, 0), (p-1, 1)):
                        slots = [((a*i+b) % p, m) for i, m in enumerate(mult)]
                        assert greedy_powers(p, slots, t) == predicted
                        residue_checks += 1
            assert max(values) == bound(p, t)
        for t in range(2, p + 2):
            f = {0: 5, 1: -6, 2: 1} if (p, t) == (2, 3) else product_witness(p, t)
            assert len(f) <= t and max(f) == bound(p, t)
            if p > 2:
                assert disk_count(f, p, Fraction(1, p-2), True) == max(f)
            assert disk_count(f, p, Fraction(1, p-1), False) == max(f)
            assert any(squarefree_mod(f, q) for q in (29, 31, 37, 41, 43, 47, 53))
            products += 1
        f = jump_witness(p)
        assert len(f) <= p+2 and max(f) == p**2
        assert disk_count(f, p, Fraction(1, p-1), False) == p**2
        assert any(squarefree_mod(f, q) for q in (29, 31, 37, 41, 43, 47, 53))
        print(f"p={p:2d}: B(p+1)={bound(p,p+1):3d}, B(p+2)={p**2:3d}")
    print(f"Diagram maxima: {profiles} partitions.")
    print(f"Frobenius basis: {residue_checks} independent jet-rank comparisons.")
    print(f"Shifted Newton polygons and separability: {products} product/binomial "
          "witnesses and 8 jump witnesses.")


if __name__ == "__main__":
    main()
