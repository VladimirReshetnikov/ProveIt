#!/usr/bin/env python3
"""Exact finite checks for 'Standard Integers in a Single Infinite Interval'.

These tests verify finite polynomial certificates, not quantified theorems
about all elements of an infinite structure. Python 3.10+, standard library.
"""
from __future__ import annotations

import argparse
import json
import random
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Poly:
    """A rational polynomial in increasing coefficient order.

    Integer-constant membership is checked separately: intermediate
    computations are allowed in Q[X]. The order has X positive infinite.
    """
    coefficients: tuple[F, ...]

    @staticmethod
    def make(values: Iterable[int | F]) -> Poly:
        c = [F(x) for x in values]
        while c and c[-1] == 0:
            c.pop()
        return Poly(tuple(c))

    @staticmethod
    def integer(n: int) -> Poly:
        return Poly.make([n])

    @property
    def constant(self) -> F:
        return self.coefficients[0] if self.coefficients else F(0)

    @property
    def in_ring(self) -> bool:
        return self.constant.denominator == 1

    @property
    def degree(self) -> int:
        return len(self.coefficients) - 1

    @property
    def sign(self) -> int:
        if not self.coefficients:
            return 0
        return 1 if self.coefficients[-1] > 0 else -1

    def __add__(self, other: Poly) -> Poly:
        n = max(len(self.coefficients), len(other.coefficients))
        return Poly.make(
            (self.coefficients[i] if i < len(self.coefficients) else 0)
            + (other.coefficients[i] if i < len(other.coefficients) else 0)
            for i in range(n)
        )

    def __neg__(self) -> Poly:
        return Poly.make(-x for x in self.coefficients)

    def __sub__(self, other: Poly) -> Poly:
        return self + (-other)

    def __mul__(self, other: Poly) -> Poly:
        if not self.coefficients or not other.coefficients:
            return Poly.make([])
        out = [F(0)] * (len(self.coefficients) + len(other.coefficients) - 1)
        for i, a in enumerate(self.coefficients):
            for j, b in enumerate(other.coefficients):
                out[i + j] += a * b
        return Poly.make(out)

    def divide_scalar(self, n: int) -> Poly:
        if n == 0:
            raise ZeroDivisionError("Polynomial scalar denominator is zero")
        return Poly.make(a / n for a in self.coefficients)

    def le(self, other: Poly) -> bool:
        return (other - self).sign >= 0

    def evaluate(self, n: int) -> F:
        result = F(0)
        for a in reversed(self.coefficients):
            result = result * n + a
        return result

    def encode(self) -> list[str]:
        return [str(x) for x in self.coefficients]


ZERO, ONE, TWO, THREE = [Poly.integer(n) for n in range(4)]
X = Poly.make([0, 1])


def division(p: Poly, n: int) -> tuple[Poly, int]:
    if not p.in_ring or n < 1:
        raise ValueError("Expected an integer-constant polynomial and n >= 1")
    r = int(p.constant) % n
    q = (p - Poly.integer(r)).divide_scalar(n)
    assert q.in_ring
    assert Poly.integer(n) * q + Poly.integer(r) == p
    return q, r


def odd_factor_certificate(y: Poly) -> tuple[Poly, Poly]:
    """Produce u, v in A0 with y = (2u+3)v and 0 <= u,v <= y."""
    if not y.in_ring or y.degree < 1 or y.sign != 1:
        raise ValueError("y must be an integer-constant positive infinite polynomial")
    m = int(y.constant)
    if m == 0:
        u, v = ZERO, y.divide_scalar(3)
    else:
        k, n = 0, abs(m)
        while n % 2 == 0:
            k += 1
            n //= 2
        b = y.divide_scalar(2**k)
        u, v = (b - THREE).divide_scalar(2), Poly.integer(2**k)
    assert u.in_ring and v.in_ring
    assert ZERO.le(u) and ZERO.le(v)
    assert u.le(y) and v.le(y)
    assert (TWO * u + THREE) * v == y
    return u, v


def finite_power_predicate(y: int) -> bool:
    # Equivalent to the bounded formula over the actual finite interval [0,y].
    return y > 0 and all(y % d != 0 for d in range(3, y + 1, 2))


def random_poly(rng: random.Random, constant: int, positive: bool = True) -> Poly:
    d = rng.randrange(1, 7)
    c = [F(constant)] + [F(rng.randrange(-50, 51), rng.randrange(1, 24))
                          for _ in range(d - 1)]
    leading = F(rng.randrange(1, 51), rng.randrange(1, 24))
    c.append(leading if positive else -leading)
    return Poly.make(c)


def run(seed: int = 20261003) -> dict:
    rng = random.Random(seed)
    counts = {"infinite_odd_factor_certificates": 0, "division_certificates": 0,
              "character_identities": 0, "finite_power_checks": 0,
              "finite_standard_cut_checks": 0, "distinct_kernel_checks": 0}
    constants = [0, 1, -1, 12, -12, 2**100, -(2**100), 3 * 2**80]
    constants += [rng.randrange(-500, 501) for _ in range(1992)]
    examples = []
    for idx, constant in enumerate(constants):
        y = random_poly(rng, constant)
        u, v = odd_factor_certificate(y)
        counts["infinite_odd_factor_certificates"] += 1
        if idx < 8:
            examples.append({"y": y.encode(), "u": u.encode(), "v": v.encode()})
        p = y if idx % 2 else -y
        for n in (1, 2, 3, 5, 12, 31):
            q, r = division(p, n)
            assert 0 <= r < n
            assert p.constant == n * q.constant + r
            counts["division_certificates"] += 1
        z = random_poly(rng, rng.randrange(-40, 41), positive=bool(idx % 2))
        assert (p + z).constant == p.constant + z.constant
        assert (p * z).constant == p.constant * z.constant
        counts["character_identities"] += 2

    powers = []
    for n in range(1025):
        p = finite_power_predicate(n)
        assert p == (n > 0 and n & (n - 1) == 0)
        counts["finite_power_checks"] += 1
        if p:
            powers.append(n)
        standard = n == 0 or any(y <= n < 2 * y for y in powers)
        assert standard
        counts["finite_standard_cut_checks"] += 1

    # X-a lies in ker(ev_a) but not in ker(ev_b) whenever a != b.
    for a in range(-8, 9):
        for b in range(-8, 9):
            if a != b:
                witness = X - Poly.integer(a)
                assert witness.evaluate(a) == 0
                assert witness.evaluate(b) == b - a != 0
                counts["distinct_kernel_checks"] += 1

    return {"status": "PASS", "seed": seed, "counts": counts,
            "scope": "Exact finite certificates and finite-instance checks; not formal verification.",
            "polynomial_encoding": "Coefficients in increasing degree order, exact rational strings.",
            "examples": examples}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "counts": report["counts"]}, indent=2))


if __name__ == "__main__":
    main()
