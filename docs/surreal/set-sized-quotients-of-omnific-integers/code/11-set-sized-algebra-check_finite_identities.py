#!/usr/bin/env python3
"""Exact finite checks accompanying 'What Set-Sized Algebra Can See ...'.

Python >= 3.10, standard library only. No infinite Hahn sum, class-cardinality
argument, or theorem is proved by this program. Exponents are rational pairs
with lexicographic order; coefficients are exact Gaussian rationals.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from random import Random


@dataclass(frozen=True)
class Gaussian:
    re: F = F(0)
    im: F = F(0)

    def __add__(self, other: Gaussian) -> Gaussian:
        return Gaussian(self.re + other.re, self.im + other.im)

    def __neg__(self) -> Gaussian:
        return Gaussian(-self.re, -self.im)

    def __sub__(self, other: Gaussian) -> Gaussian:
        return self + (-other)

    def __mul__(self, other: Gaussian) -> Gaussian:
        return Gaussian(self.re * other.re - self.im * other.im,
                        self.re * other.im + self.im * other.re)

    def conjugate(self) -> Gaussian:
        return Gaussian(self.re, -self.im)


Exponent = tuple[F, F]
Series = dict[Exponent, Gaussian]
ZERO_EXP: Exponent = (F(0), F(0))
ZERO = Gaussian()
ONE = Gaussian(F(1))


def exp_add(a: Exponent, b: Exponent) -> Exponent:
    return a[0] + b[0], a[1] + b[1]


def exp_scale(n: int, a: Exponent) -> Exponent:
    return n * a[0], n * a[1]


def clean(s: Series) -> Series:
    return {g: c for g, c in s.items() if c != ZERO}


def add(x: Series, y: Series) -> Series:
    out = dict(x)
    for g, c in y.items():
        out[g] = out.get(g, ZERO) + c
    return clean(out)


def neg(x: Series) -> Series:
    return {g: -c for g, c in x.items()}


def mul(x: Series, y: Series) -> Series:
    out: Series = {}
    for g, c in x.items():
        for h, d in y.items():
            k = exp_add(g, h)
            out[k] = out.get(k, ZERO) + c * d
    return clean(out)


def shift(x: Series, g: Exponent) -> Series:
    return {exp_add(h, g): c for h, c in x.items()}


def conjugate(x: Series) -> Series:
    return {g: c.conjugate() for g, c in x.items()}


def constant(x: Series) -> Gaussian:
    return x.get(ZERO_EXP, ZERO)


def augmentation(x: Series) -> Gaussian:
    out = ZERO
    for c in x.values():
        out = out + c
    return out


def random_series(rng: Random, allow_constant: bool) -> Series:
    out: Series = {}
    for _ in range(rng.randint(1, 6)):
        g = (F(rng.randint(1, 4)), F(rng.randint(-5, 5), rng.randint(1, 3)))
        c = Gaussian(F(rng.randint(-4, 4), rng.randint(1, 3)),
                     F(rng.randint(-3, 3), rng.randint(1, 3)))
        out[g] = out.get(g, ZERO) + c
    if allow_constant:
        out[ZERO_EXP] = Gaussian(F(rng.randint(-4, 4)), F(rng.randint(-4, 4)))
    return clean(out)


def run_checks(seed: int, cases: int) -> dict:
    rng = Random(seed)
    counts: dict[str, int] = {}

    def check(name: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(f"Failed exact check: {name}")
        counts[name] = counts.get(name, 0) + 1

    for _ in range(cases):
        s = random_series(rng, allow_constant=False)
        b: Exponent = (F(0), F(rng.randint(1, 5), rng.randint(1, 3)))
        a = exp_add(b, (F(0), F(rng.randint(1, 5), rng.randint(1, 3))))
        d = exp_add(a, exp_scale(-1, b))
        denominator = add({a: ONE}, {b: -ONE})
        q: Series = {}
        for n in range(9):
            offset = exp_add(exp_scale(-1, a), exp_scale(-n, d))
            q = add(q, shift(s, offset))
            residual = shift(s, exp_scale(-(n + 1), d))
            rhs = add(s, neg(residual))
            check("finite_geometric_remainder", mul(denominator, q) == rhs)
            check("positive_quotient_support", all(g > ZERO_EXP for g in q))

        x = random_series(rng, allow_constant=True)
        y = random_series(rng, allow_constant=True)
        check("constant_additive", constant(add(x, y)) == constant(x) + constant(y))
        check("constant_multiplicative", constant(mul(x, y)) == constant(x) * constant(y))
        check("finite_augmentation_multiplicative",
              augmentation(mul(x, y)) == augmentation(x) * augmentation(y))
        check("conjugation_multiplicative",
              conjugate(mul(x, y)) == mul(conjugate(x), conjugate(y)))
        check("shift_product", mul(shift(x, a), y) == shift(mul(x, y), a))

    # An explicit boundary witness: constant extraction is not a homomorphism
    # once negative exponents are permitted.
    u = {(F(1), F(0)): ONE}
    inv_u = {(F(-1), F(0)): ONE}
    check("whole_field_constant_counterexample",
          constant(mul(u, inv_u)) == ONE and constant(u) * constant(inv_u) == ZERO)
    check("finite_augmentation_detects_monomial",
          augmentation(u) == ONE and constant(u) == ZERO)

    # Exhaustive ordinary Gaussian derivation check in F_2, with i acting as 1.
    for a in range(2):
        for b in range(2):
            for c in range(2):
                for d in range(2):
                    deriv_product = (a * d + b * c) % 2
                    leibniz = ((a + b) * d + (c + d) * b) % 2
                    check("gaussian_F2_derivation", deriv_product == leibniz)

    return {
        "status": "PASS",
        "seed": seed,
        "random_cases": cases,
        "checks_by_family": counts,
        "total_exact_checks": sum(counts.values()),
        "arithmetic": "Exact Gaussian rational coefficients and lexicographic Q^2 exponents",
        "scope": "Finite identities and boundary examples only",
        "not_verified": ["Infinite Hahn summability", "Class cardinalities",
                         "Universal homomorphism theorem", "Historical novelty", "Lean formalization"]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260922)
    parser.add_argument("--cases", type=int, default=80)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.cases < 1:
        parser.error("--cases must be positive")
    result = run_checks(args.seed, args.cases)
    text = json.dumps(result, indent=2) + "\n"
    print(text, end="")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
