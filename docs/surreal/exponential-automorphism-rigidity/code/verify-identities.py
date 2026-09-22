#!/usr/bin/env python3
"""Exact finite checks accompanying Growth-Scale Rigidity.

Run with Python 3.10+; only the standard library is used.
These checks do NOT construct No, verify an exponential on a Hahn field,
check infinite supports, or constitute a proof of the manuscript's theorems.
They check the finite identities and finite Hahn substitutions used in them.
"""
from __future__ import annotations

from fractions import Fraction as Q
import random
import unittest
from collections.abc import Callable

Gamma = tuple[Q, Q, Q]  # lexicographically ordered additive group Q^3
Series = dict[Gamma, Q]  # FINITE support only
ZERO: Gamma = (Q(0), Q(0), Q(0))
SEED = 20260921
TRIALS = 300


def gadd(a: Gamma, b: Gamma) -> Gamma:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def gsub(a: Gamma, b: Gamma) -> Gamma:
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def reweight(g: Gamma, weights: Gamma) -> Gamma:
    if any(w <= 0 for w in weights):
        raise ValueError("Weights must be strictly positive.")
    return (g[0] * weights[0], g[1] * weights[1], g[2] * weights[2])


def clean(s: Series) -> Series:
    return {g: a for g, a in s.items() if a != 0}


def add(s: Series, t: Series) -> Series:
    out = dict(s)
    for g, a in t.items():
        out[g] = out.get(g, Q(0)) + a
    return clean(out)


def mul(s: Series, t: Series) -> Series:
    out: Series = {}
    for g, a in s.items():
        for h, b in t.items():
            k = gadd(g, h)
            out[k] = out.get(k, Q(0)) + a * b
    return clean(out)


def lift(s: Series, transform: Callable[[Gamma], Gamma]) -> Series:
    out: Series = {}
    for g, a in s.items():
        k = transform(g)
        out[k] = out.get(k, Q(0)) + a
    return clean(out)


def sign(s: Series) -> int:
    s = clean(s)
    if not s:
        return 0
    leading_coefficient = s[min(s)]
    return 1 if leading_coefficient > 0 else -1


def rq(rng: random.Random) -> Q:
    return Q(rng.randint(-9, 9), rng.randint(1, 7))


def rg(rng: random.Random) -> Gamma:
    return (rq(rng), rq(rng), rq(rng))


def rs(rng: random.Random) -> Series:
    out: Series = {}
    for _ in range(rng.randint(1, 7)):
        g, a = rg(rng), rq(rng)
        out[g] = out.get(g, Q(0)) + a
    return clean(out)


class FiniteChecks(unittest.TestCase):
    def setUp(self) -> None:
        self.rng = random.Random(SEED)

    def test_01_twisted_leibniz(self) -> None:
        # A and B stand for the images of a and b. Multiplicativity
        # then fixes the image of ab to A*B. No automorphism of Q is claimed.
        for _ in range(TRIALS):
            a, A, b, B = (rq(self.rng) for _ in range(4))
            self.assertEqual(A * B - a * b, A * (B - b) + b * (A - a))

    def test_02_two_probe_inequality(self) -> None:
        for _ in range(TRIALS):
            a, A = rq(self.rng), rq(self.rng)
            if a == A:
                A += 1
            threshold = abs(rq(self.rng)) + Q(1, 7)
            d = A - a
            b = 2 * threshold * (1 + abs(A)) / abs(d)
            # Probe image S is free; the inequality holds for every S.
            S = rq(self.rng)
            Db, Dab = S - b, A * S - a * b
            self.assertGreater(max(abs(Db), abs(Dab)), threshold)

    def test_03_value_group_reweighting(self) -> None:
        weights = (Q(3, 2), Q(1), Q(2))
        inverse = tuple(1 / q for q in weights)
        for _ in range(TRIALS):
            g, h = rg(self.rng), rg(self.rng)
            self.assertEqual(reweight(gadd(g, h), weights),
                             gadd(reweight(g, weights), reweight(h, weights)))
            self.assertEqual(reweight(reweight(g, weights), inverse), g)
            self.assertEqual(g < h, reweight(g, weights) < reweight(h, weights))
        with self.assertRaises(ValueError):
            reweight(ZERO, (Q(1), Q(0), Q(1)))

    def test_04_finite_hahn_lift(self) -> None:
        weights = (Q(1), Q(1), Q(2))
        inverse = (Q(1), Q(1), Q(1, 2))
        T = lambda g: reweight(g, weights)
        Ti = lambda g: reweight(g, inverse)
        for _ in range(TRIALS):
            s, t = rs(self.rng), rs(self.rng)
            self.assertEqual(lift(add(s, t), T), add(lift(s, T), lift(t, T)))
            self.assertEqual(lift(mul(s, t), T), mul(lift(s, T), lift(t, T)))
            self.assertEqual(lift(lift(s, T), Ti), s)
            self.assertEqual(sign(lift(s, T)), sign(s))
            if s:
                self.assertEqual(min(lift(s, T)), T(min(s)))

    def test_05_bounded_layer_and_coarsening(self) -> None:
        # Interpret (a,b,c) as a*omega^2+b*omega+c in the value group.
        # Doubling c changes it by less than omega, at every rational c.
        bound: Gamma = (Q(0), Q(1), Q(0))
        weights = (Q(1), Q(1), Q(2))
        for _ in range(TRIALS):
            g, h = rg(self.rng), rg(self.rng)
            Tg = reweight(g, weights)
            d = gsub(Tg, g)
            self.assertLess(max(d, tuple(-q for q in d)), bound)
            # Quotient by the last layer is represented by the first two.
            self.assertEqual(Tg[:2], g[:2])
            self.assertEqual(gadd(g, h)[:2],
                             (g[0] + h[0], g[1] + h[1]))

    def test_06_rational_dilation_polynomial(self) -> None:
        for _ in range(TRIALS):
            r, x, e, f = (rq(self.rng) for _ in range(4))
            self.assertEqual((r * x + e) ** 2 - (r * x ** 2 + f),
                             (r ** 2 - r) * x ** 2 + 2 * r * x * e + e ** 2 - f)
        # The finite algebraic equation r^2-r=0 has roots 0 and 1.
        for numerator in range(-10, 11):
            for denominator in range(1, 8):
                r = Q(numerator, denominator)
                self.assertEqual(r * r - r == 0, r in (0, 1))

    def test_07_complex_norm_product(self) -> None:
        for _ in range(TRIALS):
            a, b, c, d = (rq(self.rng) for _ in range(4))
            self.assertEqual((a*c - b*d)**2 + (a*d + b*c)**2,
                             (a*a + b*b) * (c*c + d*d))


if __name__ == "__main__":
    print("Exact finite checks: Python standard library / rational arithmetic")
    print(f"Deterministic seed: {SEED}; trials per randomized test: {TRIALS}")
    print("Scope: algebraic identities and FINITE Hahn analogues only.")
    print("Not a proof assistant or implementation of No.\n", flush=True)
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(FiniteChecks)
    outcome = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if outcome.wasSuccessful() else 1)
