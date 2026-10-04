#!/usr/bin/env python3
"""Exact finite regression tests for surreal_self_embeddings.tex.

These are NOT proofs about arbitrary surreal numbers, ordinal-length signs,
set-sized Hahn sums, class recursion, or elementary embeddings.  All tests
use finite sign sequences and finite formal Hahn polynomials with rational
coefficients.  They check formulas and catch elementary implementation errors.

Run with Python 3.10+; only the standard library is required.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import comb
from random import Random
from typing import Callable, Iterable
import json
import sys

RationalMap = Callable[[Q], Q]
CHECKS = 0


def check(condition: bool, description: str) -> None:
    global CHECKS
    CHECKS += 1
    if not condition:
        raise AssertionError(description)


def compression(x: Q) -> Q:
    return x / (1 + abs(x))


def fminus(x: Q) -> Q:
    return x / (1 - x) if x < 0 else x


def fgap(x: Q) -> Q:
    return x + (1 if x < 0 else 2)


def sign_compare(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    """First difference, treating an absent sign as zero."""
    for i in range(max(len(a), len(b))):
        av = a[i] if i < len(a) else 0
        bv = b[i] if i < len(b) else 0
        if av != bv:
            return 1 if av > bv else -1
    return 0


def is_prefix(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return len(a) <= len(b) and b[: len(a)] == a


@dataclass(frozen=True)
class H1:
    """Finite sum of c_a W^a with rational a and c_a."""
    terms: tuple[tuple[Q, Q], ...] = ()

    @staticmethod
    def make(terms: Iterable[tuple[Q, Q]]) -> H1:
        acc: dict[Q, Q] = {}
        for exponent, coefficient in terms:
            exponent, coefficient = Q(exponent), Q(coefficient)
            acc[exponent] = acc.get(exponent, Q(0)) + coefficient
        return H1(tuple(sorted(((a, c) for a, c in acc.items() if c), reverse=True)))

    @staticmethod
    def constant(c: Q | int) -> H1:
        return H1.make([(Q(0), Q(c))])

    def __add__(self, other: H1) -> H1:
        return H1.make((*self.terms, *other.terms))

    def __neg__(self) -> H1:
        return H1.make((a, -c) for a, c in self.terms)

    def __sub__(self, other: H1) -> H1:
        return self + (-other)

    def __mul__(self, other: H1) -> H1:
        return H1.make((a + b, c * d) for a, c in self.terms for b, d in other.terms)

    def __lt__(self, other: H1) -> bool:
        difference = self - other
        return bool(difference.terms and difference.terms[0][1] < 0)

    def relocate(self, f: RationalMap) -> H1:
        return H1.make((f(a), c) for a, c in self.terms)

    def has_only_constant_support(self) -> bool:
        return all(a == 0 for a, _ in self.terms)


@dataclass(frozen=True)
class H2:
    """Finite sum of c_a W^a, where each a is itself an H1 polynomial."""
    terms: tuple[tuple[H1, Q], ...] = ()

    @staticmethod
    def make(terms: Iterable[tuple[H1, Q]]) -> H2:
        acc: dict[H1, Q] = {}
        for exponent, coefficient in terms:
            coefficient = Q(coefficient)
            acc[exponent] = acc.get(exponent, Q(0)) + coefficient
        return H2(tuple(sorted(((a, c) for a, c in acc.items() if c),
                               key=lambda item: item[0], reverse=True)))

    @staticmethod
    def constant(c: Q | int) -> H2:
        return H2.make([(H1(), Q(c))])

    def __add__(self, other: H2) -> H2:
        return H2.make((*self.terms, *other.terms))

    def __neg__(self) -> H2:
        return H2.make((a, -c) for a, c in self.terms)

    def __sub__(self, other: H2) -> H2:
        return self + (-other)

    def __mul__(self, other: H2) -> H2:
        return H2.make((a + b, c * d) for a, c in self.terms for b, d in other.terms)

    def __lt__(self, other: H2) -> bool:
        difference = self - other
        return bool(difference.terms and difference.terms[0][1] < 0)

    def double_lift(self, f: RationalMap) -> H2:
        return H2.make((a.relocate(f), c) for a, c in self.terms)


def random_h1(rng: Random) -> H1:
    return H1.make((Q(rng.randrange(-5, 6), rng.randrange(1, 4)),
                    Q(rng.randrange(-4, 5), rng.randrange(1, 4)))
                   for _ in range(rng.randrange(5)))


def random_h2(rng: Random) -> H2:
    return H2.make((random_h1(rng), Q(rng.randrange(-4, 5), rng.randrange(1, 4)))
                   for _ in range(rng.randrange(5)))


# Formal coefficient-polynomial Taylor twist, for D(b)=1.
# A key (a,k) represents b^k W^a.  Only k>=0 is admitted.
Poly = dict[tuple[Q, int], Q]


def poly_clean(p: Poly) -> Poly:
    return {key: value for key, value in p.items() if value}


def poly_mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for (a, k), c in p.items():
        for (b, m), d in q.items():
            key = (a + b, k + m)
            out[key] = out.get(key, Q(0)) + c * d
    return poly_clean(out)


def taylor_twist(p: Poly, sign: int = 1) -> Poly:
    if sign not in (-1, 1):
        raise ValueError("sign must be -1 or +1")
    out: Poly = {}
    for (a, k), c in p.items():
        if k < 0:
            raise ValueError("This finite test allows polynomial coefficients only")
        for n in range(k + 1):
            key = (a - n, k - n)
            out[key] = out.get(key, Q(0)) + c * comb(k, n) * sign**n
    return poly_clean(out)


def main() -> None:
    rng = Random(20261003)
    signs = [s for n in range(6) for s in product((-1, 1), repeat=n)]
    prefix = (1, -1, 1)
    block = lambda s: tuple(v for sign in s for v in (sign, sign))
    for a in signs:
        for b in signs:
            check(sign_compare(prefix + a, prefix + b) == sign_compare(a, b),
                  "prefix order preservation/reflection")
            check(is_prefix(prefix + a, prefix + b) == is_prefix(a, b),
                  "prefix simplicity preservation/reflection")
            check(sign_compare(block(a), block(b)) == sign_compare(a, b),
                  "block order preservation/reflection")
            check(is_prefix(block(a), block(b)) == is_prefix(a, b),
                  "block simplicity preservation/reflection")

    samples = sorted({Q(n, d) for n in range(-12, 13) for d in range(1, 6)})
    for f in (compression, fminus, fgap):
        for a, b in zip(samples, samples[1:]):
            check(f(a) < f(b), "rational order map is increasing")
    for x in samples:
        check(abs(compression(x)) < 1, "compression has bounded range")
        y = compression(x)
        check(y / (1 - abs(y)) == x, "compression inverse")
        it = x
        for n in range(13):
            check(it == x / (1 + n * abs(x)), "exact compression iterate")
            it = compression(it)
        check(fgap(x) != x, "gap map has no fixed points")

    omega = H1.make([(Q(1), Q(1))])
    check((omega * omega).relocate(compression)
          != omega.relocate(compression) * omega.relocate(compression),
          "first compression lift is not multiplicative")

    shift = lambda x: x + 1
    composite = lambda x: shift(compression(x))
    for _ in range(240):
        a, b = random_h1(rng), random_h1(rng)
        check((a + b).relocate(compression)
              == a.relocate(compression) + b.relocate(compression),
              "first lift is additive")
        check((a * b).relocate(lambda x: 2 * x)
              == a.relocate(lambda x: 2 * x) * b.relocate(lambda x: 2 * x),
              "additive exponent transport is multiplicative")
        check((a < b) == (a.relocate(compression) < b.relocate(compression)),
              "first lift is ordered")

        x, y = random_h2(rng), random_h2(rng)
        for f in (compression, fminus, fgap):
            check((x + y).double_lift(f) == x.double_lift(f) + y.double_lift(f),
                  "double lift is additive")
            check((x * y).double_lift(f) == x.double_lift(f) * y.double_lift(f),
                  "double lift is multiplicative")
            check((x < y) == (x.double_lift(f) < y.double_lift(f)),
                  "double lift is ordered")
            check(H2.constant(1).double_lift(f) == H2.constant(1),
                  "double lift is unital")
        check(x.double_lift(compression).double_lift(shift) == x.double_lift(composite),
              "double lift composition law")
        check((x.double_lift(compression) == x)
              == all(a.has_only_constant_support() for a, _ in x.terms),
              "compression fixed-support formula")
        check((x.double_lift(fgap) == x) == all(a == H1() for a, _ in x.terms),
              "gap lift fixed field is the coefficient field")

    for _ in range(120):
        ordinal_exponent = H1.make((Q(rng.randrange(6)), Q(rng.randrange(1, 5)))
                                  for _ in range(rng.randrange(1, 6)))
        ordinal_polynomial = H2.make([(ordinal_exponent, Q(2)), (H1(), Q(3))])
        check(ordinal_polynomial.double_lift(fminus) == ordinal_polynomial,
              "finite ordinal-polynomial samples are fixed")
        p = poly_clean({(Q(rng.randrange(-3, 4)), rng.randrange(5)):
                        Q(rng.randrange(-3, 4)) for _ in range(5)})
        q = poly_clean({(Q(rng.randrange(-3, 4)), rng.randrange(5)):
                        Q(rng.randrange(-3, 4)) for _ in range(5)})
        check(taylor_twist(taylor_twist(p), -1) == p, "formal Taylor inverse")
        check(taylor_twist(poly_mul(p, q)) == poly_mul(taylor_twist(p), taylor_twist(q)),
              "formal Taylor multiplicativity")

    report = {
        "status": "PASS",
        "checks": CHECKS,
        "random_seed": 20261003,
        "sign_sequences_tested": len(signs),
        "python": sys.version.split()[0],
        "scope": "Exact finite rational/sign/Hahn-polynomial regression checks only",
        "not_verified": ["arbitrary ordinal signs", "infinite Hahn summability",
                         "class recursion", "elementary embeddings", "Lean compilation"],
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
