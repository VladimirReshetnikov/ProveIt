#!/usr/bin/env python3
"""Exact reference algorithms for Section 4, using only integer arithmetic.

This is an executable companion, not a proof checker or a substitute for
the mathematical proofs.  All range searches used here have explicit bounds.
Coefficient order: X0^2, X0*X1, X0*X2, X1^2, X1*X2, X2^2.
"""

from itertools import product
from math import gcd, isqrt


def primitive(v):
    """Canonical primitive representative: first nonzero coordinate positive."""
    v = tuple(v)
    g = 0
    for x in v:
        g = gcd(g, abs(x))
    if g == 0:
        raise ValueError("a projective vector must be nonzero")
    w = tuple(x // g for x in v)
    first = next(x for x in w if x)
    return w if first > 0 else tuple(-x for x in w)


def height(v):
    return max(map(abs, primitive(v)))


def evaluate(q, x):
    a00, a01, a02, a11, a12, a22 = q
    x0, x1, x2 = x
    return (a00 * x0 * x0 + a01 * x0 * x1 + a02 * x0 * x2
            + a11 * x1 * x1 + a12 * x1 * x2 + a22 * x2 * x2)


def polar_determinant(q):
    a00, a01, a02, a11, a12, a22 = q
    return (8*a00*a11*a22 + 2*a01*a02*a12
            - 2*a00*a12*a12 - 2*a11*a02*a02 - 2*a22*a01*a01)


class PointedConic:
    def __init__(self, q, seed):
        if len(q) != 6 or len(seed) != 3:
            raise ValueError("six coefficients and three seed coordinates required")
        self.q = tuple(q)
        self.seed = primitive(seed)
        if evaluate(self.q, self.seed) != 0:
            raise ValueError("seed is not a point on the conic")
        if polar_determinant(self.q) == 0:
            raise ValueError("the conic must be nonsingular")
        j = next(i for i in range(3) if self.seed[i])
        self.perm = (j,) + tuple(i for i in range(3) if i != j)
        self.p = tuple(self.seed[i] for i in self.perm)
        # Evaluate the quadratic in permuted coordinates without division.
        def q_new(x):
            y = [0, 0, 0]
            for i, original in enumerate(self.perm):
                y[original] = x[i]
            return evaluate(self.q, y)
        self.a = q_new((0, 1, 0))
        self.c = q_new((0, 0, 1))
        self.b = q_new((0, 1, 1)) - self.a - self.c
        p0, p1, p2 = self.p
        self.ell = q_new((p0, p1+1, p2)) - self.a
        self.m = q_new((p0, p1, p2+1)) - self.c
        self.r = (self.a*self.m*self.m - self.b*self.ell*self.m
                  + self.c*self.ell*self.ell)
        if self.r == 0:
            raise AssertionError("determinant identity violated")
        self.C = sum(map(abs, self.q))
        self.P = max(map(abs, self.p))
        Ds = (self.m*self.m + abs(self.b*self.m-self.c*self.ell)
              + abs(self.c*self.m))
        Dt = (self.ell*self.ell + abs(self.a*self.ell)
              + abs(self.b*self.ell-self.a*self.m))
        self.D = max(Ds, Dt)
        self.A = 3*self.C*self.P
        self.K = 2*self.P*self.D

    def parameter(self, parameter):
        s, t = primitive(parameter)
        L = self.ell*s+self.m*t
        R = self.a*s*s+self.b*s*t+self.c*t*t
        p0, p1, p2 = self.p
        new = (-p0*R, -p1*R+s*L, -p2*R+t*L)
        original = [0, 0, 0]
        for i, j in enumerate(self.perm):
            original[j] = new[i]
        return primitive(original)

    def inverse(self, point):
        point = primitive(point)
        if evaluate(self.q, point) != 0:
            raise ValueError("input is not a point on the conic")
        x0, x1, x2 = (point[i] for i in self.perm)
        p0, p1, p2 = self.p
        v, w = p0*x1-p1*x0, p0*x2-p2*x0
        return primitive((v, w) if (v or w) else (-self.m, self.ell))

    def points_up_to_height(self, bound):
        """Complete enumeration via the proved inverse height bound."""
        if bound < 0:
            raise ValueError("height bound must be nonnegative")
        limit = isqrt(self.K*bound)
        result = set()
        for s in range(-limit, limit+1):
            for t in range(-limit, limit+1):
                if (s or t) and (s, t) == primitive((s, t)):
                    point = self.parameter((s, t))
                    if height(point) <= bound:
                        result.add(point)
        return sorted(result)


def brute_points(q, bound):
    """Independent exhaustive projective-box enumerator for regression checks."""
    return sorted(x for x in product(range(-bound, bound+1), repeat=3)
                  if any(x) and x == primitive(x) and evaluate(q, x) == 0)


def validate():
    fixtures = [
        ((1, 0, 0, 1, 0, -1), (1, 0, 1)),
        ((1, 0, 0, 1, 0, -1), (3, 4, 5)),
        ((1, 0, 0, -1, 0, -1), (1, 0, 1)),
        ((0, 1, 0, 0, 0, -1), (0, 1, 0)),
        ((0, 1, 0, 1, 3, -2), (1, 0, 0)),
    ]
    cases = 0
    enumerations = 0
    for q, seed in fixtures:
        conic = PointedConic(q, seed)
        assert conic.parameter((-conic.m, conic.ell)) == primitive(seed)
        for s, t in product(range(-15, 16), repeat=2):
            if not (s or t):
                continue
            parameter = primitive((s, t))
            point = conic.parameter(parameter)
            assert evaluate(q, point) == 0
            assert conic.inverse(point) == parameter
            assert height(parameter)**2 <= conic.K*height(point)
            assert height(point) <= conic.A*height(parameter)**2
            cases += 1
        # The enumeration route is deliberately different from the raw box.
        for bound in range(1, 5):
            assert conic.points_up_to_height(bound) == brute_points(q, bound)
            enumerations += 1
    for n in range(1, 101):
        count = sum(gcd(s, t) == 1 for s in range(1, n+1)
                    for t in range(1, n+1))
        assert 4*count >= n*n
    # The obstruction is modulo 9 with primitivity at 3, not absence of F3 points.
    primitive_mod9 = [x for x in product(range(9), repeat=3)
                     if any(y % 3 for y in x)]
    assert not any((x*x+y*y-3*z*z) % 9 == 0
                   for x, y, z in primitive_mod9)
    return {"parameter_checks": cases, "complete_enumeration_checks": enumerations,
            "coprime_count_checks": 100,
            "primitive_mod9_vectors_checked": len(primitive_mod9)}


if __name__ == "__main__":
    import json
    print(json.dumps(validate(), sort_keys=True, indent=2))
