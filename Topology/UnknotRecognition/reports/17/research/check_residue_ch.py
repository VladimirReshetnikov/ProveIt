"""Independent sparse coefficient oracle for the residue CH research notes.

Standard library only. This is mathematical verification, not a production
cobordism backend. It deliberately uses exponent tuples and ordinary modular
integers instead of the recognizer's packed F2 ring representation.
"""

from itertools import permutations, product
import json
from pathlib import Path
import random


class Ring:
    def __init__(self, p, b):
        self.p, self.b = p, b
        self.zero = {}
        self.one = {(0,) * b: 1}
        self.monomials = tuple(product(range(p), repeat=b))

    def add(self, a, b):
        out = dict(a)
        for k, v in b.items():
            w = (out.get(k, 0) + v) % self.p
            if w:
                out[k] = w
            else:
                out.pop(k, None)
        return out

    def scale(self, a, c):
        return {k: w for k, v in a.items() if (w := v * c % self.p)}

    def mul(self, a, b):
        out = {}
        for u, c in a.items():
            for v, d in b.items():
                k = tuple(x + y for x, y in zip(u, v))
                if max(k, default=0) >= self.p:
                    continue
                z = (out.get(k, 0) + c * d) % self.p
                if z:
                    out[k] = z
                else:
                    out.pop(k, None)
        return out

    def var(self, i):
        k = [0] * self.b
        k[i] = 1
        return {tuple(k): 1}

    def residue(self, a):
        return a.get((0,) * self.b, 0)

    def random(self, rng, radical=False):
        return {
            k: c for k in self.monomials
            if (not radical or any(k)) and rng.random() < .3
            and (c := rng.randrange(self.p))
        }


def identity(r, ring):
    return [[dict(ring.one) if i == j else {} for j in range(r)] for i in range(r)]


def zero(r):
    return [[{} for _ in range(r)] for _ in range(r)]


def madd(a, b, ring):
    return [[ring.add(x, y) for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mscale(a, c, ring):
    return [[ring.scale(x, c) for x in ar] for ar in a]


def mmul(a, b, ring):
    r = len(a)
    c = zero(r)
    for i in range(r):
        for j in range(r):
            for k in range(r):
                c[i][j] = ring.add(c[i][j], ring.mul(a[i][k], b[k][j]))
    return c


def mpow(a, n, ring):
    out = identity(len(a), ring)
    while n:
        if n & 1:
            out = mmul(out, a, ring)
        n //= 2
        if n:
            a = mmul(a, a, ring)
    return out


def peval(poly, a, ring):
    out = zero(len(a))
    eye = identity(len(a), ring)
    for c in reversed(poly):
        out = madd(mmul(out, a, ring), mscale(eye, c, ring), ring)
    return out


def ptrim(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return a


def padd(a, b, p):
    out = list(a) + [0] * max(0, len(b) - len(a))
    for i, x in enumerate(b):
        out[i] = (out[i] + x) % p
    return ptrim(out)


def pscale(a, c, p):
    return ptrim([x * c % p for x in a])


def pmul(a, b, p):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return ptrim(out)


def pdivmod(a, b, p):
    a, b = ptrim(a), ptrim(b)
    if not b:
        raise ZeroDivisionError
    q = [0] * max(0, len(a) - len(b) + 1)
    inv = pow(b[-1], -1, p)
    while len(a) >= len(b):
        d, c = len(a) - len(b), a[-1] * inv % p
        q[d] = c
        for i, x in enumerate(b):
            a[d + i] = (a[d + i] - c * x) % p
        a = ptrim(a)
    return ptrim(q), a


def pinv(a, modulus, p):
    r0, r1 = modulus, a
    s0, s1 = [], [1]
    while r1:
        q, r2 = pdivmod(r0, r1, p)
        r0, r1 = r1, r2
        s0, s1 = s1, padd(s0, pscale(pmul(q, s1, p), -1, p), p)
    if len(r0) != 1:
        raise ValueError("not coprime")
    return pdivmod(pscale(s0, pow(r0[0], -1, p), p), modulus, p)[1]


def frobenius_poly(a, p):
    out = [0] * ((len(a) - 1) * p + 1)
    for i, c in enumerate(a):
        out[i * p] = c
    return out


def characteristic_residue(a, ring):
    """Small independent Leibniz determinant, safe in every characteristic."""
    r, p = len(a), ring.p
    out = []
    for perm in permutations(range(r)):
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(r) for j in range(i + 1, r))
        term = [sign % p]
        for i, j in enumerate(perm):
            f = [(-ring.residue(a[i][j])) % p]
            if i == j:
                f.append(1)
            term = pmul(term, f, p)
        out = padd(out, term, p)
    return out


def fitting_polynomials(chi, p):
    a = next(i for i, c in enumerate(chi) if c)
    q = chi[a:]
    f = frobenius_poly(chi, p)
    if a == len(chi) - 1:
        return a, [0], [0]
    if a == 0:
        return a, [1], pinv([0, 1], f, p)
    nil = [0] * (p * a) + [1]
    unit = frobenius_poly(q, p)
    e = pmul(nil, pinv(nil, unit, p), p)
    z = pdivmod(pmul(e, pinv([0, 1], unit, p), p), f, p)[1]
    return a, e, z


def sharp_matrix(p, b, r):
    ring = Ring(p, b)
    s = min(b, r)
    out = zero(r)
    for i in range(s):
        out[i][i] = ring.var(i)
    labels = [j for j in range(s, b) for _ in range(p - 1)]
    labels = labels[:s - 1]
    labels += [j for j in range(s) for _ in range(p - 1)][:s - 1 - len(labels)]
    for i, j in enumerate(labels):
        out[i][i + 1] = ring.var(j)
    return ring, out


def verify_a(a, ring, counts):
    r, p, b = len(a), ring.p, ring.b
    chi = characteristic_residue(a, ring)
    f = frobenius_poly(chi, p)
    assert peval(f, a, ring) == zero(r)
    counts["annihilators"] += 1
    nil_dim, ep, zp = fitting_polynomials(chi, p)
    e, d = peval(ep, a, ring), peval(zp, a, ring)
    eye = identity(r, ring)
    nilproj = madd(eye, mscale(e, -1, ring), ring)
    assert mmul(e, e, ring) == e
    assert mmul(a, d, ring) == e == mmul(d, a, ring)
    assert mmul(d, e, ring) == d == mmul(e, d, ring)
    assert mmul(mpow(a, p * nil_dim, ring), nilproj, ring) == zero(r)
    counts["fitting_and_drazin"] += 1
    if chi[0]:
        inv = zero(r)
        for i in range(1, r + 1):
            inv = madd(inv, mscale(mpow(a, p * i - 1, ring),
                                  -pow(chi[0], -1, p) * chi[i], ring), ring)
        assert mmul(a, inv, ring) == eye == mmul(inv, a, ring)
        counts["closed_inverses"] += 1
    if all(not ring.residue(x) for row in a for x in row):
        cutoff = min(b * (p - 1) + 1, p * r)
        assert mpow(a, cutoff, ring) == zero(r)
        counts["radical_cutoffs"] += 1


def main():
    rng = random.Random(20261008)
    counts = dict(annihilators=0, fitting_and_drazin=0, closed_inverses=0,
                  radical_cutoffs=0, sharpness=0, nilpotent_residue_sharpness=0)

    # All 2 by 2 matrices over F2[x]/x^2, including every residue type.
    ring = Ring(2, 1)
    elements = [{k: 1 for i, k in enumerate(ring.monomials) if (bits >> i) & 1}
                for bits in range(4)]
    for entries in product(elements, repeat=4):
        verify_a([list(entries[:2]), list(entries[2:])], ring, counts)

    for p, b, max_r, cases in [(2, 2, 4, 20), (2, 3, 4, 20),
                               (3, 2, 4, 15), (3, 3, 3, 8), (5, 2, 3, 8)]:
        ring = Ring(p, b)
        for r in range(1, max_r + 1):
            for i in range(cases):
                radical = i % 3 == 0
                a = [[ring.random(rng, radical) for _ in range(r)] for _ in range(r)]
                verify_a(a, ring, counts)

    # Sharpness uniformly across both b-driven and r-driven regimes.
    for p in (2, 3, 5):
        for b in range(1, 8):
            for r in range(1, 7):
                ring, a = sharp_matrix(p, b, r)
                cutoff = min(b * (p - 1) + 1, p * r)
                assert mpow(a, cutoff - 1, ring) != zero(r)
                assert mpow(a, cutoff, ring) == zero(r)
                counts["sharpness"] += 1

    for p in (2, 3, 5):
        ring = Ring(p, 1)
        for r in range(1, 7):
            a = zero(r)
            for i in range(r - 1):
                a[i][i + 1] = dict(ring.one)
            a[r - 1][0] = ring.var(0)
            assert mpow(a, p * r - 1, ring) != zero(r)
            assert mpow(a, p * r, ring) == zero(r)
            counts["nilpotent_residue_sharpness"] += 1

    result = {"seed": 20261008, "status": "PASS", "counts": counts,
              "scope": "Independent finite algebra checks; no topology verdicts."}
    output = Path(__file__).with_name("residue_ch_checks.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
