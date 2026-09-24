#!/usr/bin/env python3
"""Exact finite checks accompanying Strong Hahn Measures on Surreal Workspaces.

Python 3.10+; standard library only.  No floating-point arithmetic is used in
series calculations.  This is a finite-support test harness, NOT an implementation
of arbitrary Hahn series and NOT a proof of any infinite summability statement.
Run from any directory: python3 /path/to/code/verify.py
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import random
import sys
from typing import Iterable, Mapping

Exponent = tuple[Q, ...]

@dataclass
class Series:
    """Finite rational-coefficient series; tuple exponents have lexicographic order."""
    rank: int
    terms: dict[Exponent, Q]

    def __post_init__(self) -> None:
        if self.rank < 1:
            raise ValueError("Rank must be positive")
        cleaned: dict[Exponent, Q] = {}
        for exponent, coefficient in self.terms.items():
            exponent = tuple(Q(v) for v in exponent)
            if len(exponent) != self.rank:
                raise ValueError("Wrong exponent rank")
            coefficient = Q(coefficient)
            if coefficient:
                cleaned[exponent] = cleaned.get(exponent, Q(0)) + coefficient
        self.terms = {e: c for e, c in cleaned.items() if c}

    @classmethod
    def zero(cls, rank: int = 1) -> Series:
        return cls(rank, {})

    @classmethod
    def constant(cls, value: int | Q, rank: int = 1) -> Series:
        return cls(rank, {(Q(0),) * rank: Q(value)})

    @classmethod
    def monomial(cls, exponent: int | Q | Exponent,
                 coefficient: int | Q = 1) -> Series:
        if not isinstance(exponent, tuple):
            exponent = (Q(exponent),)
        return cls(len(exponent), {exponent: Q(coefficient)})

    def _same_rank(self, other: Series) -> None:
        if self.rank != other.rank:
            raise ValueError("Cannot combine different ranks")

    def __add__(self, other: Series) -> Series:
        self._same_rank(other)
        result = dict(self.terms)
        for e, c in other.terms.items():
            result[e] = result.get(e, Q(0)) + c
        return Series(self.rank, result)

    def __neg__(self) -> Series:
        return Series(self.rank, {e: -c for e, c in self.terms.items()})

    def __sub__(self, other: Series) -> Series:
        return self + (-other)

    def __mul__(self, other: Series) -> Series:
        self._same_rank(other)
        result: dict[Exponent, Q] = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                ef = tuple(x + y for x, y in zip(e, f))
                result[ef] = result.get(ef, Q(0)) + c * d
        return Series(self.rank, result)

    def coeff(self, exponent: int | Q | Exponent) -> Q:
        if not isinstance(exponent, tuple):
            exponent = (Q(exponent),)
        return self.terms.get(exponent, Q(0))

    def sign(self) -> int:
        if not self.terms:
            return 0
        leading = self.terms[min(self.terms)]
        return 1 if leading > 0 else -1


def add_all(values: Iterable[Series], rank: int = 1) -> Series:
    result = Series.zero(rank)
    for value in values:
        result = result + value
    return result


def multiply_all(values: Iterable[Series], rank: int = 1) -> Series:
    result = Series.constant(1, rank)
    for value in values:
        result = result * value
    return result


class Checks:
    def __init__(self) -> None:
        self.counts: dict[str, int] = {}

    def check(self, group: str, condition: bool, description: str) -> None:
        if not condition:
            raise AssertionError(f"{group}: {description}")
        self.counts[group] = self.counts.get(group, 0) + 1


def cylinder(atoms: Mapping[tuple[int, ...], Series], word: tuple[int, ...],
             rank: int = 1) -> Series:
    return add_all((weight for path, weight in atoms.items()
                    if path[:len(word)] == word), rank)


def test_scalar_half_bound(checks: Checks, rng: random.Random) -> None:
    group = "finite scalar nonvanishing probability bound"
    dimension = 6
    for _ in range(30):
        coefficients = [Q(rng.randint(-3, 3)) for _ in range(dimension)]
        if all(c == 0 for c in coefficients):
            coefficients[0] = Q(1)
        nonzero = sum(
            sum((c * bit for c, bit in zip(coefficients, bits)), Q(0)) != 0
            for bits in product((0, 1), repeat=dimension)
        )
        checks.check(group, nonzero >= 2 ** (dimension - 1),
                     "a nonzero finite linear form must be nonzero on at least half the masks")


def test_coherent_trees(checks: Checks, rng: random.Random) -> None:
    group = "finite coefficient trees and reconstruction"
    depth = 7
    exponents = [Q(-2), Q(0), Q(1, 3), Q(1), Q(5, 2)]
    all_paths = list(product((0, 1), repeat=depth))
    for _ in range(20):
        paths = rng.sample(all_paths, 8)
        atoms = {
            path: Series(1, {(e,): Q(rng.randint(-3, 3)) for e in exponents})
            for path in paths
        }
        levels = [
            {word: cylinder(atoms, word) for word in product((0, 1), repeat=n)}
            for n in range(depth + 1)
        ]
        for n in range(depth):
            for word, value in levels[n].items():
                checks.check(group,
                             value == levels[n + 1][word + (0,)] + levels[n + 1][word + (1,)],
                             "parent must equal the sum of its children")
        for e in exponents:
            widths = [sum(value.coeff(e) != 0 for value in level.values()) for level in levels]
            atom_count = sum(w.coeff(e) != 0 for w in atoms.values())
            for left, right in zip(widths, widths[1:]):
                checks.check(group, left <= right, "active widths are monotone")
            checks.check(group, all(w <= atom_count for w in widths),
                         "active widths are bounded by the coefficient atom count")
            checks.check(group, widths[-1] == atom_count,
                         "separating level recovers every coefficient atom")
        for path, weight in atoms.items():
            checks.check(group, levels[-1][path] == weight, "separating cylinders recover weights")


def check_bernoulli(checks: Checks, probabilities: list[Series]) -> None:
    group = "finite independent products and first-error recovery"
    n = len(probabilities)
    one = Series.constant(1)
    base = [one - p for p in probabilities]
    all_base = multiply_all(base)
    atoms: dict[tuple[int, ...], Series] = {}
    for bits in product((0, 1), repeat=n):
        weight = multiply_all(probabilities[j] if bit else base[j]
                              for j, bit in enumerate(bits))
        atoms[bits] = weight
        checks.check(group, weight.sign() >= 0, "finite independent weights are nonnegative")
        # Cross-multiplied version of U * product(p/(1-p)); no truncated inverse.
        left = weight * multiply_all(base[j] for j, bit in enumerate(bits) if bit)
        right = all_base * multiply_all(probabilities[j] for j, bit in enumerate(bits) if bit)
        checks.check(group, left == right, "exact cross-multiplied finite-deviation identity")
    checks.check(group, add_all(atoms.values()) == one, "total mass is one")
    for depth in range(n + 1):
        for word in product((0, 1), repeat=depth):
            expected = multiply_all(probabilities[j] if bit else base[j]
                                    for j, bit in enumerate(word))
            checks.check(group, cylinder(atoms, word) == expected, "finite marginals are exact")
    survival = one
    previous_errors = Series.zero()
    for p, u in zip(probabilities, base):
        h = p * survival
        checks.check(group, survival == one - previous_errors, "finite first-error telescoping")
        checks.check(group, h == p * (one - previous_errors), "recovery after multiplication")
        previous_errors = previous_errors + h
        survival = survival * u
    checks.check(group, previous_errors + survival == one, "first error plus survival partitions total mass")


def test_hidden_negative(checks: Checks) -> None:
    group = "finite truncations of hidden-negative-atom example"
    m = 10
    length = m + 1
    zero = (0,) * length
    z = (1,) * length
    positives = [Series.monomial(Q(n, n + 1)) for n in range(1, m + 1)]
    atoms = {zero: -Series.monomial(1),
             z: Series.constant(1) - add_all(positives) + Series.monomial(1)}
    for n, weight in enumerate(positives, start=1):
        path = [0] * length
        path[n - 1] = 1
        atoms[tuple(path)] = weight
    checks.check(group, add_all(atoms.values()) == Series.constant(1), "normalization")
    checks.check(group, atoms[zero].sign() < 0, "distinguished point mass is negative")
    # This is only a finite truncation: positivity is claimed through depth m-1.
    for depth in range(m):
        for word in product((0, 1), repeat=depth):
            checks.check(group, cylinder(atoms, word).sign() >= 0,
                         "positive cylinders before the truncation cutoff")
    checks.check(group, cylinder(atoms, (0,) * m).sign() < 0,
                 "finite truncation reveals negativity at its cutoff, as it must")
    for n in range(1, m):
        expected = add_all(positives[n:]) - Series.monomial(1)
        checks.check(group, cylinder(atoms, (0,) * n) == expected,
                     "exact tail-minus-negative-atom formula")


def test_coarse_graining(checks: Checks) -> None:
    group = "rank-two coarse-graining coefficient witnesses"
    one = Series.constant(1, 2)
    half = Series.constant(Q(1, 2), 2)
    survival = one
    last_gamma: Exponent | None = None
    for n in range(1, 10):
        gamma = (Q(1), Q(1, n))
        q = Series.monomial((Q(0), Q(n)))
        tiny = Series.monomial(gamma)
        p0 = one - q
        p1 = half * (q + tiny)
        p2 = half * (q - tiny)
        for p in (p0, p1, p2):
            checks.check(group, p.sign() > 0, "all three probabilities are positive")
        checks.check(group, p0 + p1 + p2 == one, "row normalization")
        checks.check(group, p1 + p2 == q, "coarse-graining cancels the hidden exponent")
        h = p1 * survival
        checks.check(group, h.coeff(gamma) == Q(1, 2), "first-error descending coefficient is exactly 1/2")
        if last_gamma is not None:
            checks.check(group, gamma < last_gamma, "witness exponents strictly descend")
        last_gamma = gamma
        survival = survival * p0


def main() -> None:
    checks = Checks()
    rng = random.Random(20260922)
    test_scalar_half_bound(checks, rng)
    test_coherent_trees(checks, rng)
    check_bernoulli(checks, [Series.constant(Q(1, 2)), Series.constant(Q(1, 3))]
                    + [Series.monomial(n) for n in range(1, 5)])
    check_bernoulli(checks, [Series.monomial(Q(n, n + 1)) for n in range(1, 6)])
    test_hidden_negative(checks)
    test_coarse_graining(checks)
    report = {
        "status": "PASS",
        "seed": 20260922,
        "python_version": sys.version.split()[0],
        "exact_arithmetic": "fractions.Fraction; finite series; lexicographic tuple exponents",
        "groups": checks.counts,
        "total_assertions": sum(checks.counts.values()),
        "limitations": [
            "Finite tests are not proofs of the infinite theorems.",
            "Finite prefixes do not establish well ordering or eventual boundedness.",
            "The finite hidden-negative-atom truncation is positive only before its cutoff.",
            "No arbitrary infinite Hahn-series arithmetic or Lean proof checking is implemented."
        ],
    }
    root = Path(__file__).resolve().parents[1]
    data = root / "data"
    data.mkdir(exist_ok=True)
    (data / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    lines = ["PASS: exact finite verification", f"Python {report['python_version']}; seed {report['seed']}", ""]
    lines += [f"{count:6d} assertions: {group}" for group, count in checks.counts.items()]
    lines += ["", f"Total: {report['total_assertions']} assertions", "", "Scope limitations:"]
    lines += [f"- {item}" for item in report["limitations"]]
    text = "\n".join(lines) + "\n"
    (data / "verification.txt").write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
