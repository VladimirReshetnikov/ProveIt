#!/usr/bin/env python3
"""Exact finite certificates for the root-support construction.

No floating point or external packages.  This is a reference implementation,
not an iPRA proof checker.  The finite grid fallback is complete under the
written rational-descent theorem; the checks below use certified shortcuts
to avoid its deliberately enormous worst-case enumeration.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from math import ceil
import json


@dataclass(frozen=True)
class GQ:
    re: Q = Q(0)
    im: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, "re", Q(self.re))
        object.__setattr__(self, "im", Q(self.im))

    def __add__(self, other):
        other = lift(other)
        return GQ(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return GQ(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-lift(other))

    def __mul__(self, other):
        other = lift(other)
        return GQ(self.re * other.re - self.im * other.im,
                  self.re * other.im + self.im * other.re)

    __rmul__ = __mul__

    def norm_sq(self):
        return self.re * self.re + self.im * self.im

    def norm1(self):
        return abs(self.re) + abs(self.im)


def lift(x):
    return x if isinstance(x, GQ) else GQ(x)


ZERO, ONE = GQ(), GQ(1)


def poly(cs):
    return [lift(c) for c in cs]


def eval_poly(p, z):
    ans = ZERO
    for a in reversed(p):
        ans = ans * z + a
    return ans


def mul_poly(p, q):
    out = [ZERO] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] = out[i + j] + a * b
    return out


def product_poly(zs):
    ans = [ONE]
    for z in zs:
        ans = mul_poly(ans, [-z, ONE])
    return ans


def coeff_error(p, q):
    n = max(len(p), len(q))
    return sum(((p[i] if i < len(p) else ZERO)
                - (q[i] if i < len(q) else ZERO)).norm1()
               for i in range(n))


def synthetic_divide(p, z):
    assert len(p) >= 2 and p[-1] == ONE
    out = [ZERO] * (len(p) - 1)
    out[-1] = ONE
    for i in range(len(out) - 2, -1, -1):
        out[i] = p[i + 1] + z * out[i + 1]
    remainder = p[0] + z * out[0]
    reconstructed = mul_poly([-z, ONE], out)
    reconstructed[0] = reconstructed[0] + remainder
    assert reconstructed == p
    return out, remainder


def close(s, t, radius):
    radius = Q(radius)
    assert radius >= 0 and s and t
    def directed(a, b):
        return all(any((z - w).norm_sq() <= radius * radius for w in b)
                   for z in a)
    return directed(s, t) and directed(t, s)


def stable_products(s, t, radius, root_bound):
    """Check the finite stability hypotheses and conclusion independently."""
    assert len(s) == len(t) and len(s) > 0
    n, R, r = len(s), Q(root_bound), Q(radius)
    assert R >= 1 and r >= 0
    assert all(z.norm_sq() <= R * R for z in s + t)
    p, q = product_poly(s), product_poly(t)
    # The coefficient l1 upper bound is stronger than the Euclidean hypothesis.
    delta = max((a - b).norm1() for a, b in zip(p[:-1], q[:-1]))
    assert n * R ** (n - 1) * delta <= r ** n
    assert close(s, t, r)
    return delta


def sqrt_approx(c, error):
    """Rational bisection with prescribed finite iteration count."""
    c, error = Q(c), Q(error)
    assert c >= 0 and error > 0
    lo, hi = Q(0), Q(max(1, ceil(c)))
    initial_hi = hi
    # After k halvings, squared-value error <= 2*initial_hi**2 / 2**k.
    target = max(1, ceil(2 * initial_hi * initial_hi / error))
    steps = target.bit_length()
    for _ in range(steps):
        mid = (lo + hi) / 2
        if mid * mid <= c:
            lo = mid
        else:
            hi = mid
    assert abs(lo * lo - c) <= error
    return lo


def approx_root(p, eps):
    """Total bounded rational root algorithm, with exact checked shortcuts.

    Only the fallback is a generic producer.  Its completeness is proved
    in Section 4 of the report using the repository's rational descent lemma.
    The bounds are mathematically valid, not practical complexity claims.
    """
    p, eps = poly(p), Q(eps)
    assert len(p) >= 2 and p[-1] == ONE and 0 < eps <= 1
    A = max(1, ceil(max(a.norm1() for a in p)))
    R = A + 2
    def accept(z):
        return eval_poly(p, z).norm_sq() <= eps * eps

    # Every shortcut is followed by the same exact residual check.
    proposals = []
    if len(p) == 2:
        proposals.append(-p[0])
    if len(p) == 3 and p[1] == ZERO and p[0].im == 0:
        c = -p[0].re
        q = sqrt_approx(abs(c), eps)
        proposals.append(GQ(q, 0) if c >= 0 else GQ(0, q))
    lim = min(R, 4)
    proposals.extend(GQ(x, y) for x in range(-lim, lim + 1)
                     for y in range(-lim, lim + 1))
    for z in proposals:
        if accept(z):
            assert z.norm_sq() <= R * R
            return z

    # Fully bounded fallback: no unbounded precision search.
    U = 2 * R + 1
    lip = max(Q(1), sum(i * a.norm1() * U ** (i - 1)
                         for i, a in enumerate(p) if i))
    mesh_denom = ceil(4 * lip / eps)
    stop = R * mesh_denom
    for x in range(-stop, stop + 1):
        for y in range(-stop, stop + 1):
            z = GQ(Q(x, mesh_denom), Q(y, mesh_denom))
            if accept(z):
                assert z.norm_sq() <= R * R
                return z
    # A fixed default makes the implementation total on all codes.
    # Valid monic inputs cannot reach it by the written grid theorem.
    return ZERO


def approx_factor(p, eta):
    p, eta = poly(p), Q(eta)
    assert len(p) >= 2 and p[-1] == ONE and 0 < eta <= 1
    n = len(p) - 1
    A = max(1, ceil(max(a.norm1() for a in p)))
    bounds, L = [], 1
    for _ in range(n):
        bounds.append(A)
        L *= 2 * A + 5
        A = (A + 1) * (2 * A + 5) ** n
    eps = eta / (2 * n * L)
    current, roots, remainders = list(p), [], []
    for A in bounds:
        assert max(a.norm1() for a in current) <= A
        z = approx_root(current, eps)
        assert eval_poly(current, z).norm_sq() <= eps * eps
        assert z.norm_sq() <= (A + 2) ** 2
        current, rem = synthetic_divide(current, z)
        roots.append(z)
        remainders.append(rem)
    assert current == [ONE]
    assert coeff_error(p, product_poly(roots)) <= eta
    return roots, remainders


def run_checks():
    counts = {"factorizations": 0, "stability_pairs": 0,
              "collision_instances": 0, "invalid_hypotheses_rejected": 0}
    examples = [poly([-2, 0, 1]), poly([2, 0, 1]), poly([0, 0, 1]),
                product_poly([GQ(1), GQ(2), GQ(-1)]),
                product_poly([GQ(1, 1), GQ(1, -1)]),
                product_poly([GQ(0), GQ(0), GQ(1)])]
    for p in examples:
        for eta in (Q(1, 2), Q(1, 8)):
            approx_factor(p, eta)
            counts["factorizations"] += 1

    # Arbitrary labels and multiplicity collisions: all calculations exact.
    for k in range(2, 10):
        h = Q(1, 2 ** (2 * k + 6))
        cases = [([GQ(0), GQ(0)], [GQ(h), GQ(-h)]),
                 ([GQ(1), GQ(-1)], [GQ(-1 + h), GQ(1 - h)]),
                 ([GQ(0, 1), GQ(0, -1)], [GQ(h, -1), GQ(-h, 1)])]
        for s, t in cases:
            stable_products(s, t, Q(1, 2 ** k), 2)
            counts["stability_pairs"] += 1

    # Obstruction family at x=0: a changes through arbitrarily small positives.
    for k in range(0, 6):
        a = Q(1, 2 ** (2 * k))
        roots, _ = approx_factor(poly([-a, 0, 1]), Q(1, 16))
        assert close(roots, [ZERO], Q(1, 2 ** k) + Q(1, 16))
        counts["collision_instances"] += 1

    for s, t, r, R in [([GQ(0)], [GQ(1)], Q(1, 2), 1),
                        ([GQ(3)], [GQ(3)], Q(1), 1)]:
        try:
            stable_products(s, t, r, R)
        except AssertionError:
            counts["invalid_hypotheses_rejected"] += 1
        else:
            raise AssertionError("an invalid hypothesis was accepted")
    assert counts["invalid_hypotheses_rejected"] == 2
    return {"status": "passed", "scope": "Exact finite certificate checks only",
            "arithmetic": "fractions.Fraction; no floating point", "counts": counts}


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2))
