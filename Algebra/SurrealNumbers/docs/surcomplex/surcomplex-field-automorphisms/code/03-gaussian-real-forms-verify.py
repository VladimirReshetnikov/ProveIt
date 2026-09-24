#!/usr/bin/env python3
"""Exact finite regression checks for geometric symmetrization.

Python 3.9+; standard library only. No floating-point arithmetic is used.
The test algebra is Q(i)[x^Q][s]/(s^(N+1)), with finite outer support.
It is a truncated test algebra, not a representation of all Hahn series.
Run: python verify.py --output verification.json
"""
from __future__ import annotations

import argparse
import json
import platform
import random
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple


@dataclass(frozen=True)
class Gaussian:
    real: Fraction = Fraction(0)
    imag: Fraction = Fraction(0)

    def __add__(self, other: Gaussian) -> Gaussian:
        return Gaussian(self.real + other.real, self.imag + other.imag)

    def __neg__(self) -> Gaussian:
        return Gaussian(-self.real, -self.imag)

    def __sub__(self, other: Gaussian) -> Gaussian:
        return self + (-other)

    def __mul__(self, other: Gaussian) -> Gaussian:
        return Gaussian(self.real * other.real - self.imag * other.imag,
                        self.real * other.imag + self.imag * other.real)

    def scale(self, value: Fraction) -> Gaussian:
        return Gaussian(self.real * value, self.imag * value)

    def conjugate(self) -> Gaussian:
        return Gaussian(self.real, -self.imag)


ZERO = Gaussian()
ONE = Gaussian(Fraction(1))
I = Gaussian(Fraction(0), Fraction(1))
HALF_I = I.scale(Fraction(1, 2))
Polynomial = Tuple[Gaussian, ...]
Series = Dict[Fraction, Polynomial]


def canonical(f: Series) -> Series:
    return {a: p for a, p in f.items() if any(c != ZERO for c in p)}


def add(f: Series, g: Series, n: int) -> Series:
    zero = (ZERO,) * (n + 1)
    return canonical({a: tuple(x + y for x, y in
                              zip(f.get(a, zero), g.get(a, zero)))
                      for a in f.keys() | g.keys()})


def negate(f: Series) -> Series:
    return {a: tuple(-c for c in p) for a, p in f.items()}


def multiply_polynomials(p: Polynomial, q: Polynomial, n: int) -> Polynomial:
    out = [ZERO] * (n + 1)
    for r in range(n + 1):
        if p[r] == ZERO:
            continue
        for s in range(n + 1 - r):
            if q[s] != ZERO:
                out[r + s] = out[r + s] + p[r] * q[s]
    return tuple(out)


def multiply(f: Series, g: Series, n: int) -> Series:
    out: Series = {}
    zero = (ZERO,) * (n + 1)
    for a, p in f.items():
        for b, q in g.items():
            prod = multiply_polynomials(p, q, n)
            out[a + b] = tuple(u + v for u, v in zip(out.get(a + b, zero), prod))
    return canonical(out)


def monomial(a: Fraction, b: int, n: int) -> Series:
    if not 0 <= b <= n:
        raise ValueError("The truncated test algebra requires 0 <= b <= N.")
    p = [ZERO] * (n + 1)
    p[b] = ONE
    return {a: tuple(p)}


def exponential(z: Gaussian, n: int) -> Polynomial:
    """Coefficients of exp(z*s) modulo s^(n+1)."""
    out = [ONE]
    for r in range(1, n + 1):
        out.append((out[-1] * z).scale(Fraction(1, r)))
    return tuple(out)


def flow(f: Series, lam: Gaussian, n: int) -> Series:
    return canonical({a: multiply_polynomials(p, exponential(lam.scale(a), n), n)
                      for a, p in f.items()})


def conjugation(f: Series) -> Series:
    return {a: tuple(c.conjugate() for c in p) for a, p in f.items()}


def involution(f: Series, n: int) -> Series:
    return flow(conjugation(f), I, n)


def normalizer(f: Series, n: int) -> Series:
    return flow(f, HALF_I, n)


def remainder(f: Series, n: int) -> Series:
    return add(normalizer(f, n), negate(f), n)


def geometric_inverse(f: Series, n: int) -> Tuple[Series, Series]:
    """Return sum_{r=0}^N (-T)^r(f) and the next (zero) term."""
    out: Series = {}
    term = f
    for _ in range(n + 1):
        out = add(out, term, n)
        term = negate(remainder(term, n))
    return out, term


def value(f: Series) -> Tuple[Fraction, int]:
    if not f:
        raise ValueError("Zero has no finite leading exponent.")
    return min((a, b) for a, p in f.items()
               for b, c in enumerate(p) if c != ZERO)


def random_series(rng: random.Random, n: int) -> Series:
    out: Series = {}
    for a in rng.sample([Fraction(j, 2) for j in range(-4, 5)], 3):
        p = [ZERO] * (n + 1)
        for b in range(min(3, n) + 1):
            p[b] = Gaussian(Fraction(rng.randint(-2, 2), rng.randint(1, 3)),
                            Fraction(rng.randint(-2, 2), rng.randint(1, 3)))
        out[a] = tuple(p)
    return canonical(out)


def run_checks(n: int = 8, samples: int = 24) -> dict:
    if n < 2 or samples < 1:
        raise ValueError("Use N >= 2 and at least one random sample.")
    counts: Dict[str, int] = {}

    def check(group: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(f"Failed check in {group}, after {counts.get(group, 0)} passes.")
        counts[group] = counts.get(group, 0) + 1

    # Individual monomials, including half-exponents, test the actual normalizer formula.
    for a in [Fraction(j, 2) for j in range(-4, 5)]:
        f = monomial(a, 0, n)
        half = monomial(a / 2, 0, n)
        orbit_product = multiply(half, involution(half, n), n)
        check("orbit_product_formula", orbit_product == normalizer(f, n))
        check("monomial_involution", involution(involution(f, n), n) == f)
        check("monomial_intertwining", involution(normalizer(f, n), n)
              == normalizer(conjugation(f), n))

    rng = random.Random(20260923)
    for _ in range(samples):
        f = random_series(rng, n)
        g = random_series(rng, n)
        lam = Gaussian(Fraction(rng.randint(-2, 2), 2), Fraction(1, 3))
        mu = Gaussian(Fraction(1, 4), Fraction(rng.randint(-2, 2), 2))
        check("flow_composition", flow(flow(f, lam, n), mu, n) == flow(f, lam + mu, n))
        check("flow_multiplicativity", flow(multiply(f, g, n), lam, n)
              == multiply(flow(f, lam, n), flow(g, lam, n), n))
        check("involution", involution(involution(f, n), n) == f)
        check("intertwining", involution(normalizer(f, n), n)
              == normalizer(conjugation(f), n))
        check("normalizer_multiplicativity", normalizer(multiply(f, g, n), n)
              == multiply(normalizer(f, n), normalizer(g, n), n))
        inv, next_term = geometric_inverse(f, n)
        check("geometric_inverse", inv == flow(f, -HALF_I, n))
        check("nilpotent_remainder", not next_term)
        check("left_inverse", normalizer(inv, n) == f)
        check("right_inverse", geometric_inverse(normalizer(f, n), n)[0] == f)
        check("conjugacy_identity", flow(involution(normalizer(f, n), n), -HALF_I, n)
              == conjugation(f))
        check("leading_value", value(normalizer(f, n)) == value(f))

    # Support-sign tests are separate from truncation and include negative inner exponents.
    for a in [Fraction(-2), Fraction(-1, 2), Fraction(0)]:
        for b in range(-4, 5):
            if (a, b) >= (Fraction(0), 0):
                continue
            for r in range(n + 1):
                # The r>0 coefficient is zero when a=0.
                if a == 0 and r > 0:
                    continue
                check("negative_support_preservation", (a, b + r) < (Fraction(0), 0))

    return {
        "status": "passed",
        "python": platform.python_version(),
        "arithmetic": "exact fractions in Q(i); no floating point",
        "test_algebra": "finite outer support in Q(i)[x^Q][s]/(s^(N+1))",
        "N": n,
        "seed": 20260923,
        "random_samples": samples,
        "checks_by_group": counts,
        "total_assertions": sum(counts.values()),
        "limitations": [
            "Finite regression tests only; not a proof of Hahn summability.",
            "No verification of class-sized constructions or cardinality theorems.",
            "No Lean formalization or repository build was performed.",
            "These tests do not model arbitrary Gaussian-omnific automorphisms."
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    parser.add_argument("--order", type=int, default=8)
    parser.add_argument("--samples", type=int, default=24)
    args = parser.parse_args()
    try:
        result = run_checks(args.order, args.samples)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    except (AssertionError, ValueError, OSError) as exc:
        raise SystemExit(f"Verification failed: {exc}") from exc
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
