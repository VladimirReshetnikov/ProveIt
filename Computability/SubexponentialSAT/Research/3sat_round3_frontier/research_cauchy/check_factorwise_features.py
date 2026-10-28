"""Independent modular audit; no imported/supplied research code is executed.

Arithmetic is (Z/2^p)[U]/(U^2+U+1).  Features are evaluated solely by
integer power extraction and unit inversion, never by dividing residues.
"""
import json
import math
from pathlib import Path


def v2(n):
    if n == 0:
        raise ValueError("zero has no finite valuation")
    return (abs(n) & -abs(n)).bit_length() - 1


class Ring:
    def __init__(self, p):
        self.p, self.m = p, 1 << p

    def z(self, a):
        if isinstance(a, int):
            return (a % self.m, 0)
        return tuple(x % self.m for x in a)

    def add(self, a, b):
        return ((a[0] + b[0]) % self.m, (a[1] + b[1]) % self.m)

    def mul(self, a, b):
        u, v = a
        x, y = b
        return ((u*x-v*y) % self.m, (u*y+v*x-v*y) % self.m)

    def scale(self, a, n):
        return ((a[0]*n) % self.m, (a[1]*n) % self.m)

    def inv(self, a):
        u, v = a
        norm = (u*u-u*v+v*v) % self.m
        if norm % 2 == 0:
            raise ValueError("nonunit inversion attempted")
        return self.scale(self.z((u-v, -v)), pow(norm, -1, self.m))

    def val(self, a):
        return min([v2(x) for x in a if x] + [self.p])


def slots(a, i):
    R = 1 << i
    return [j % R + 2*R*(j//R) for j in range(1 << (a-1))]


def factorial_val(q):
    return q - q.bit_count()


def normalized_den(ring, t, a, zeta, difference):
    """Return d, (T+difference)/2^d computed from integer inputs."""
    i = v2(t)
    nu = i if difference == 0 else min(i, v2(difference))
    u = ring.add(ring.z((t+difference)//(1 << nu)),
                 ring.scale(zeta, 1 << (a+1-nu)))
    if ring.val(u) != 0:
        raise ValueError("denominator valuation lemma failed")
    return nu, u


def feature(ring, t, a, zeta, S, b, j, transpose=False):
    if j < b:
        return ring.z(0)
    i, R = v2(t), 1 << v2(t)
    q = b // R
    E = q + factorial_val(q)
    sign = -1 if transpose else 1
    nu, unit = normalized_den(ring, t, a, zeta, sign*(S[j]-S[b]))
    _, Tunit = normalized_den(ring, t, a, zeta, 0)
    value, exponent = ring.mul(Tunit, ring.inv(unit)), i-nu
    for h in range(b):
        n = sign*(S[j]-S[h])
        nval = v2(n)
        dval, dunit = normalized_den(ring, t, a, zeta, n)
        exponent += nval-dval
        value = ring.mul(value, ring.mul(ring.z(n//(1 << nval)), ring.inv(dunit)))
    if exponent < E:
        raise ValueError("factorial valuation inequality failed")
    return ring.scale(value, 1 << (exponent-E))


def gamma_unit(ring, t, a, zeta):
    """Gamma(T) = 2^(a+1) zeta * return_value; only unit inversion."""
    L = 1 << a
    deriv = math.prod(-v for v in range(-L, L) if v != 0)
    deriv_val = v2(deriv)
    value = ring.z(1)
    val_sum = 0
    for v in range(-L, L):
        if v == t:
            continue
        nu = v2(t-v)
        val_sum += nu
        term = ring.add(ring.z((t-v)//(1 << nu)), ring.scale(zeta, 1 << (a+1-nu)))
        value = ring.mul(value, term)
    if val_sum != deriv_val:
        raise ValueError("grid product valuation mismatch")
    return ring.mul(value, ring.inv(ring.z(deriv//(1 << deriv_val))))


def check():
    counts = dict(configurations=0, entries=0, precision_truncations=0,
                  integral_features=0, unit_diagonals=0, sparse_bilinear_checks=0)
    for a in range(1, 6):
        L = 1 << a
        for i in range(a):
            candidates = sorted(set([-(1 << i), 1 << i, L-(1 << i)]))
            for t in candidates:
                for z in [(0, 0), (1, 0), (0, 1), (1, 1), (2, 3)]:
                    ring = Ring(37)
                    zeta = ring.z(z)
                    S, R = slots(a, i), 1 << i
                    n = len(S)
                    F = [[feature(ring, t, a, zeta, S, b, j) for b in range(n)] for j in range(n)]
                    G = [[feature(ring, t, a, zeta, S, b, j, True) for j in range(n)] for b in range(n)]
                    counts['integral_features'] += 2*n*n
                    for b in range(n):
                        if ring.val(F[b][b]) or ring.val(G[b][b]):
                            raise ValueError("normalized diagonal not a unit")
                        counts['unit_diagonals'] += 2
                    gu = gamma_unit(ring, t, a, zeta)
                    _, tu = normalized_den(ring, t, a, zeta, 0)
                    gamma_over_T = ring.scale(ring.mul(ring.mul(zeta, gu), ring.inv(tu)), 1 << (a+1-i))
                    A = [[ring.scale(ring.mul(gamma_over_T, F[j][b]), 1 << (2*((b//R)+factorial_val(b//R)))) for b in range(n)] for j in range(n)]
                    W = []
                    for j in range(n):
                        row = []
                        for k in range(n):
                            nu, du = normalized_den(ring, t, a, zeta, S[j]-S[k])
                            direct = ring.scale(ring.mul(ring.mul(zeta, gu), ring.inv(du)), 1 << (a+1-nu))
                            total = ring.z(0)
                            for b in range(n):
                                total = ring.add(total, ring.mul(A[j][b], G[b][k]))
                            if total != direct:
                                raise ValueError(("full factorization mismatch", a, i, t, z, j, k))
                            counts['entries'] += 1
                            for p in [1, 2, 5, 9, 17]:
                                trunc = ring.z(0)
                                for b in range(n):
                                    q = b//R
                                    weight = a+1-i+2*q+2*factorial_val(q)
                                    if weight < p:
                                        trunc = ring.add(trunc, ring.mul(A[j][b], G[b][k]))
                                if any((trunc[c]-direct[c]) % (1 << p) for c in [0, 1]):
                                    raise ValueError("modular truncation mismatch")
                                counts['precision_truncations'] += 1
                            row.append(direct)
                        W.append(row)
                    # Missing real ports and nontrivial scalar coefficients.
                    xx = [((j*3+1) % 5) if j % 3 else 0 for j in range(n)]
                    yy = [((j*2+1) % 7) if j % 4 else 0 for j in range(n)]
                    direct = ring.z(0)
                    sep = ring.z(0)
                    for j in range(n):
                        for k in range(n):
                            direct = ring.add(direct, ring.scale(W[j][k], xx[j]*yy[k]))
                    for b in range(n):
                        left, right = ring.z(0), ring.z(0)
                        for j in range(n):
                            left = ring.add(left, ring.scale(A[j][b], xx[j]))
                            right = ring.add(right, ring.scale(G[b][j], yy[j]))
                        sep = ring.add(sep, ring.mul(left, right))
                    if direct != sep:
                        raise ValueError("sparse bilinear factorization mismatch")
                    counts['sparse_bilinear_checks'] += 1
                    counts['configurations'] += 1
    return {"status": "PASS", "arithmetic": "(Z/2^37)[U]/(U^2+U+1)",
            "no_nonunit_residue_division": True, "counts": counts,
            "limitations": "Finite local tests, not an end-to-end SAT execution or an asymptotic proof."}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2, sort_keys=True))
