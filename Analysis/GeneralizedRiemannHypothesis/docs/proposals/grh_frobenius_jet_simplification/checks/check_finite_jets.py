#!/usr/bin/env python3
"""Exact finite-ring regression checks for the Frobenius-jet proposal.

No external packages. All calculations take place in
  (F_p[epsilon]/epsilon^2)[z_1,...,z_n]/(z_1,...,z_n)^(B+1).
The nilpotent coefficient epsilon deliberately prevents any hidden use of
reducedness, perfectness, or injectivity of Frobenius. These finite tests are
regressions, not a replacement for the proofs in the report or the Lean file.
"""

from __future__ import annotations

import json
import random
from dataclasses import dataclass
from pathlib import Path

SEED = 9050035


@dataclass(frozen=True)
class JetRing:
    p: int
    n: int
    bound: int

    def clean(self, terms):
        return {
            k: v % self.p for k, v in terms.items()
            if v % self.p and k[0] < 2 and sum(k[1:]) <= self.bound
        }

    def scalar(self, a, eps=0):
        return self.clean({(0,) * (self.n + 1): a,
                           (1,) + (0,) * self.n: eps})

    def variable(self, j):
        k = [0] * (self.n + 1)
        k[j + 1] = 1
        return self.clean({tuple(k): 1})

    def add(self, *polys):
        ans = {}
        for poly in polys:
            for k, v in poly.items():
                ans[k] = ans.get(k, 0) + v
        return self.clean(ans)

    def scale(self, a, poly):
        return self.clean({k: a * v for k, v in poly.items()})

    def sub(self, x, y):
        return self.add(x, self.scale(-1, y))

    def mul(self, x, y):
        ans = {}
        for k, v in x.items():
            for ell, w in y.items():
                key = tuple(a + b for a, b in zip(k, ell))
                if key[0] < 2 and sum(key[1:]) <= self.bound:
                    ans[key] = ans.get(key, 0) + v * w
        return self.clean(ans)

    def power(self, poly, n):
        assert n >= 0
        ans = self.scalar(1)
        while n:
            if n & 1:
                ans = self.mul(ans, poly)
            n //= 2
            if n:
                poly = self.mul(poly, poly)
        return ans

    def derivative(self, poly, j, output_bound=None):
        dest = self if output_bound is None else JetRing(self.p, self.n, output_bound)
        ans = {}
        for k, v in poly.items():
            if k[j + 1]:
                ell = list(k)
                ell[j + 1] -= 1
                key = tuple(ell)
                ans[key] = ans.get(key, 0) + v * k[j + 1]
        return dest.clean(ans)

    def sum(self, polys):
        return self.add(*list(polys))

    def random_linear(self, rng):
        return self.sum(self.mul(self.scalar(rng.randrange(self.p), rng.randrange(self.p)),
                                 self.variable(j)) for j in range(self.n))

    def random_augmentation(self, rng):
        if self.bound == 0:
            return {}
        terms = {}
        for _ in range(8):
            degree = rng.randint(1, min(self.bound, 5))
            k = [rng.randrange(2)] + [0] * self.n
            for __ in range(degree):
                k[1 + rng.randrange(self.n)] += 1
            terms[tuple(k)] = rng.randrange(self.p)
        return self.clean(terms)


def length_for(q, bound):
    h, power = 0, 1
    while power <= bound:
        h += 1
        power *= q
    return h


def resolvent(ring, poly, r):
    q = ring.p ** r
    return ring.sum(ring.power(poly, q ** a)
                    for a in range(length_for(q, ring.bound)))


def moment(ring, forms, weights, e):
    return ring.sum(ring.scale(m, ring.power(L, ring.p ** e + 1))
                    for m, L in zip(weights, forms))


def raw_exponent(ring, forms, weights, r):
    ys = [resolvent(ring, L, r) for L in forms]
    if r == 2:
        return ring.sum(ring.scale(m, ring.power(Y, ring.p + 1))
                        for m, Y in zip(weights, ys))
    half = pow(2, -1, ring.p)
    return ring.sum(ring.scale(m, ring.sub(ring.power(Y, 2),
                                          ring.scale(half, ring.power(L, 2))))
                    for m, L, Y in zip(weights, forms, ys))


def paired_exponent(ring, forms, weights, r):
    h = length_for(ring.p ** r, ring.bound)
    cache = {}

    def M(e):
        if e not in cache:
            cache[e] = moment(ring, forms, weights, e)
        return cache[e]

    if r == 2:
        return ring.sum(ring.power(M(abs((2*a + 1) - 2*b)),
                                   ring.p ** min(2*a + 1, 2*b))
                        for a in range(h) for b in range(h))
    ans = ring.sum(ring.power(M(abs(a-b)), ring.p ** min(a, b))
                   for a in range(h) for b in range(h))
    return ring.sub(ans, ring.scale(pow(2, -1, ring.p), M(0)))


def assert_equal(left, right, label):
    if left != right:
        raise AssertionError(f"{label}: unequal exact polynomials\n{left}\n{right}")


def run(output=None):
    rng = random.Random(SEED)
    counts = {"pairing": 0, "resolvent": 0, "uniqueness": 0,
              "inert_exponent": 0, "ramified_exponent": 0,
              "gradient": 0, "negative_controls": 0}
    # Includes degree cutoffs immediately around p, p+1, p^2 and p^3.
    cases = [(3, b) for b in (0, 1, 2, 3, 4, 8, 9, 10, 26, 27, 28, 81, 82)]
    cases += [(5, b) for b in (0, 2, 4, 5, 6, 24, 25, 26)]
    cases += [(7, b) for b in (0, 2, 6, 7, 8, 48, 49, 50)]
    for p, bound in cases:
        for trial in range(3):
            ring = JetRing(p, 2, bound)
            forms = [ring.random_linear(rng) for _ in range(3)]
            weights = [rng.randrange(1, 2*p + 1) for _ in forms]
            # lambda is deliberately NOT Frobenius-fixed.
            lam = ring.scalar(1 + trial % (p-1), 1)
            for a in range(4):
                for b in range(4):
                    left = ring.sum(ring.scale(m, ring.mul(ring.power(L, p**a),
                                                           ring.power(L, p**b)))
                                    for m, L in zip(weights, forms))
                    right = ring.power(moment(ring, forms, weights, abs(a-b)),
                                       p ** min(a, b))
                    assert_equal(left, right, f"pairing p={p} B={bound} a={a} b={b}")
                    counts["pairing"] += 1
            for r in (1, 2):
                q = p**r
                for L in forms:
                    Y = resolvent(ring, L, r)
                    assert_equal(ring.sub(Y, ring.power(Y, q)), L, "resolvent")
                    counts["resolvent"] += 1
                Y0 = ring.random_augmentation(rng)
                L0 = ring.sub(Y0, ring.power(Y0, q))
                assert_equal(resolvent(ring, L0, r), Y0, "unique resolvent")
                counts["uniqueness"] += 1
                assert_equal(ring.mul(lam, raw_exponent(ring, forms, weights, r)),
                             ring.mul(lam, paired_exponent(ring, forms, weights, r)),
                             f"exponent p={p} B={bound} r={r}")
                counts["inert_exponent" if r == 2 else "ramified_exponent"] += 1

            # Calculate the exponent at B+1, then differentiate to B.
            source = JetRing(p, 2, bound + 1)
            sforms = [source.random_linear(rng) for _ in forms]
            slam = source.scalar(1, 1)
            for r in (1, 2):
                E = source.mul(slam, raw_exponent(source, sforms, weights, r))
                for j in range(2):
                    actual = source.derivative(E, j, bound)
                    summands = []
                    if r == 1:
                        summands.append(source.scale(pow(2, -1, p),
                                         source.derivative(moment(source, sforms, weights, 0),
                                                           j, bound)))
                    for e in range(1, length_for(p, bound) + 1):
                        if p**e <= bound and (r == 1 or e % 2 == 1):
                            term = source.derivative(moment(source, sforms, weights, e), j, bound)
                            summands.append(source.scale(2 if r == 1 else 1, term))
                    expected = ring.mul(ring.clean(slam), ring.sum(summands))
                    assert_equal(actual, expected, f"gradient p={p} B={bound} r={r}")
                    counts["gradient"] += 1

    # Negative controls: the checker must detect these invalid shortcuts.
    ring = JetRing(3, 1, 12)
    z = ring.variable(0)
    nonfixed_weight = ring.scalar(1, 1)
    lhs = ring.mul(nonfixed_weight, ring.mul(ring.power(z, 3), ring.power(z, 9)))
    rhs = ring.power(ring.mul(nonfixed_weight, ring.power(z, 4)), 3)
    assert lhs != rhs, "non-Frobenius-fixed weights should invalidate pairing"
    counts["negative_controls"] += 1

    ring = JetRing(3, 1, 2)
    z = ring.variable(0)
    assert raw_exponent(ring, [z], [1], 1) != {}
    assert all(moment(ring, [z], [1], e) == {} for e in range(1, 5))
    counts["negative_controls"] += 1  # The e=0 ramified condition is necessary.

    high, low = JetRing(3, 1, 4), JetRing(3, 1, 3)
    z4 = high.power(high.variable(0), 4)
    assert low.clean(z4) == {}
    assert high.derivative(z4, 0, 3) != {}
    counts["negative_controls"] += 1  # Differentiation requires B+1 precision.

    ring = JetRing(3, 1, 3)
    z3 = ring.power(ring.variable(0), 3)
    assert z3 != {} and ring.derivative(z3, 0) == {}
    counts["negative_controls"] += 1  # A gradient alone cannot certify vanishing.

    result = {"status": "PASS", "seed": SEED, "ring":
              "(F_p[epsilon]/epsilon^2)[z_1,z_2]/(z_1,z_2)^(B+1)",
              "characteristics": [3, 5, 7], "parameter_cases": len(cases),
              "trials_per_case": 3, "counts": counts,
              "total_assertion_groups": sum(counts.values()),
              "scope": "Exact finite regressions; not a full GRH build or a proof of the universal claims."}
    text = json.dumps(result, indent=2) + "\n"
    if output:
        Path(output).write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="Optional JSON results file")
    run(parser.parse_args().output)
