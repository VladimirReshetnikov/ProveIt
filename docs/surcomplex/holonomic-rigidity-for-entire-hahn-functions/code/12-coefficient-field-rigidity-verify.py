#!/usr/bin/env python3
"""Exact finite regression tests for article.tex.

Only Python's standard library is used. These tests check finite algebra and
ordered-group examples, NOT the infinite summability/transcendence theorems.
Run: python verify.py --output verification.json [--force]
"""
from __future__ import annotations

import argparse
import json
import math
import platform
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from typing import Callable

Series = list[F]
# Monomial keys: (power of z, power of jet 0, ..., power of jet s-1).
Polynomial = dict[tuple[int, ...], F]


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def equal(self, group: str, actual: object, expected: object) -> None:
        if actual != expected:
            raise AssertionError(f"{group}: {actual!r} != {expected!r}")
        self.counts[group] += 1

    def true(self, group: str, condition: bool) -> None:
        self.equal(group, condition, True)


def falling(n: int, j: int) -> int:
    if j < 0 or n < 0:
        raise ValueError("falling factorial requires nonnegative arguments")
    if n < j:
        return 0
    return math.prod(range(n - j + 1, n + 1))


def mul(a: Series, b: Series, degree: int) -> Series:
    out = [F(0)] * (degree + 1)
    for i, x in enumerate(a[:degree + 1]):
        if x:
            for j, y in enumerate(b[:degree - i + 1]):
                if y:
                    out[i + j] += x * y
    return out


def power(a: Series, n: int, degree: int) -> Series:
    out = [F(1)] + [F(0)] * degree
    for _ in range(n):
        out = mul(out, a, degree)
    return out


def jet(a: Series, lam: F, j: int, degree: int) -> Series:
    """(D^j f)(lam*z), not D^j(f(lam*z))."""
    return [a[m + j] * falling(m + j, j) * lam**m
            if m + j < len(a) else F(0) for m in range(degree + 1)]


def partial(p: Polynomial, index: int) -> Polynomial:
    out: Polynomial = {}
    for exponents, c in p.items():
        e = exponents[index + 1]
        if e:
            key = list(exponents)
            key[index + 1] -= 1
            out[tuple(key)] = c * e
    return out


def evaluate(p: Polynomial, jets: list[Series], degree: int) -> Series:
    out = [F(0)] * (degree + 1)
    for exponents, c in p.items():
        z_power = exponents[0]
        if z_power > degree:
            continue
        term = [F(1)] + [F(0)] * degree
        for values, exponent in zip(jets, exponents[1:]):
            if exponent:
                term = mul(term, power(values, exponent, degree), degree)
        for n in range(degree - z_power + 1):
            out[n + z_power] += c * term[n]
    return out


@dataclass
class Case:
    name: str
    coefficient: Callable[[int], F]
    jets: list[tuple[F, int]]
    polynomial: Polynomial


def sqrt_coefficient(n: int) -> F:
    value = F(1)
    for m in range(n):
        value *= (F(1, 2) - m) / (m + 1)
    return value


def formal_tests(check: Checks) -> list[dict[str, object]]:
    c = F(2, 3)
    cases = [
        Case("exponential", lambda n: c**n / math.factorial(n),
             [(F(1), 0), (F(1), 1)],
             {(0, 0, 1): F(1), (0, 1, 0): -c}),
        Case("Riccati", lambda n: c**n,
             [(F(1), 0), (F(1), 1)],
             {(0, 0, 1): F(1), (0, 2, 0): -c}),
        Case("algebraic square root", sqrt_coefficient,
             [(F(1), 0)],
             {(0, 2): F(1), (0, 0): F(-1), (1, 0): F(-1)}),
        Case("mixed exponential f'(2z)=f(z)^2",
             lambda n: F(1, math.factorial(n)),
             [(F(1), 0), (F(2), 1)],
             {(0, 0, 1): F(1), (0, 2, 0): F(-1)}),
        Case("mixed derivative resonance at index 2",
             lambda n: F(1, math.factorial(n)),
             [(F(1), 1), (F(2), 1)],
             {(0, 0, 1): F(1), (0, 2, 0): F(-1)}),
        Case("nonlinear dilation of a rational function",
             lambda n: F(1),
             [(F(1), 0), (F(2), 0)],
             {(0, 0, 1): F(2), (0, 1, 1): F(-1), (0, 1, 0): F(-1)}),
    ]
    for m in range(7):
        cases.append(Case(
            f"degenerate Euler monomial degree {m}",
            lambda n, m=m: F(int(n == m)),
            [(F(1), 0), (F(1), 1), (F(1), 2)],
            {(2, 1, 0, 1): F(1), (1, 1, 1, 0): F(1),
             (2, 0, 2, 0): F(-1)}))
    summaries = []
    for case in cases:
        precision = 48
        r = max(j for _, j in case.jets)
        a = [case.coefficient(n) for n in range(precision + r + 1)]
        full_jets = [jet(a, lam, j, precision) for lam, j in case.jets]
        relation = evaluate(case.polynomial, full_jets, precision)
        for n in range(precision + 1):
            check.equal("formal solution coefficients", relation[n], F(0))
        first_variations = [evaluate(partial(case.polynomial, i), full_jets,
                                     precision) for i in range(len(case.jets))]
        orders = [next((n for n, x in enumerate(s) if x), None)
                  for s in first_variations]
        ell = min(o - j for o, (_, j) in zip(orders, case.jets) if o is not None)
        constants = [s[ell + j] if ell + j >= 0 else F(0)
                     for s, (_, j) in zip(first_variations, case.jets)]
        zeros = []
        count = 0
        for n in range(r, 35):
            multiplier = sum((cij * lam**(n - j) * falling(n, j)
                              for cij, (lam, j) in zip(constants, case.jets)), F(0))
            if not multiplier:
                zeros.append(n)
            if n <= ell + 2*r or n < r:
                continue
            degree = n + ell
            truncated_jets = [jet(a[:n], lam, j, degree) for lam, j in case.jets]
            rhs = -evaluate(case.polynomial, truncated_jets, degree)[degree]
            check.equal("linearized recurrence identity", a[n] * multiplier, rhs)
            count += 1
            if multiplier:
                check.equal("coefficient recovery", rhs / multiplier, a[n])
        summaries.append({"case": case.name, "ell": ell,
                          "sampled_zero_multipliers": zeros,
                          "recurrence_coefficients_checked": count})
    return summaries


def shift_minus(sequence: list[F], lam: F) -> list[F]:
    return [sequence[n + 1] - lam * sequence[n] for n in range(len(sequence) - 1)]


def exponential_polynomial_tests(check: Checks) -> None:
    examples = [
        [(F(2), [1, -3, 2]), (F(3), [-7, 1]), (F(5), [4])],
        [(F(1), [2, -1]), (F(2), [-2, 0, 1])],
        [(F(2, 3), [1, 0, 0, 1]), (F(4, 5), [3, 1])],
        [(F(3), [0, 2, 1]), (F(7), [-1, 1, 1])],
    ]
    for terms in examples:
        seq = [sum((lam**n * sum(F(c)*n**d for d, c in enumerate(poly))
                    for lam, poly in terms), F(0)) for n in range(70)]
        for lam, poly in terms:
            for _ in range(len(poly)):
                seq = shift_minus(seq, lam)
        for x in seq:
            check.equal("exponential-polynomial annihilator", x, F(0))
    for m in range(25):
        for n in range(60):
            check.equal("degenerate Euler multiplier",
                        m*m + (1 - 2*m)*n + falling(n, 2), (n-m)**2)
    for n in range(1, 60):
        check.equal("mixed derivative multiplier scaling",
                    falling(n, 1)*(F(2)**(n-1)-2),
                    -2*falling(n, 1) + F(2)**(n-1)*falling(n, 1))


def lex_sign(v: tuple[F, ...]) -> int:
    for x in reversed(v):
        if x:
            return 1 if x > 0 else -1
    return 0


def ordered_and_boundary_tests(check: Checks) -> None:
    for d in range(2, 9):
        for level in range(d-1):
            for m in range(1, 51):
                delta = [F(0)] * d
                delta[level+1], delta[level] = F(1), F(-m)
                check.equal("successive Archimedean levels", lex_sign(tuple(delta)), 1)
        for n in range(12):
            for m in range(n+1, 12):
                # Difference of values in a lower-level subgroup minus (m-n)e_*.
                delta = tuple([F((i+1)*(m*m - 3*n)) for i in range(d-1)]
                              + [F(-(m-n))])
                check.equal("exterior descending leading values", lex_sign(delta), -1)
    for n in range(1, 201):
        check.equal("partial-theta exponent identity",
                    (n-1)*(n-2)//2 + n-1, n*(n-1)//2)
    for gamma2 in range(-20, 21):
        for beta in range(-5, 6):
            for n in range(50, 56):
                check.true("partial-theta finite escape bounds",
                           F(n*(n-1), 2) + n*F(gamma2, 2) > beta)
    seen: set[tuple[int, ...]] = set()
    for alpha in product(range(4), repeat=4):
        check.true("distinct monomial exponent vectors", alpha not in seen)
        seen.add(alpha)
    for p in [2, 3, 5, 7, 11]:
        for n in range(100):
            check.equal("positive-characteristic derivative obstruction", (p*n) % p, 0)
    for n in range(150):
        check.equal("torsion even-function identity", (-1)**(2*n), 1)
    for n in range(25):
        for j in range(6):
            for lam in [F(2), F(-3), F(2, 5)]:
                if n >= j:
                    a = [F(0)]*n + [F(7, 11)]
                    direct = jet(a, lam, j, n)[n-j]
                    expected = F(7, 11)*falling(n, j)*lam**(n-j)
                    check.equal("derivative-before-dilation convention", direct, expected)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="JSON report path; an existing file is refused unless --force")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    if args.output.exists() and not args.force:
        parser.error(f"{args.output} exists; choose a new output or pass --force")
    checks = Checks()
    cases = formal_tests(checks)
    exponential_polynomial_tests(checks)
    ordered_and_boundary_tests(checks)
    report = {
        "status": "PASS",
        "python": platform.python_version(),
        "dependencies": "Python standard library only",
        "arithmetic": "exact integers and fractions.Fraction",
        "total_checks": sum(checks.counts.values()),
        "checks_by_category": dict(sorted(checks.counts.items())),
        "formal_recurrence_cases": cases,
        "scope": [
            "Finite regression tests, not a formal verification of the article.",
            "No test establishes an infinite summability or algebraic independence theorem.",
            "Sampled zero multipliers do not constitute an effective Skolem-Mahler-Lech bound.",
            "Finite lexicographic groups test local comparisons only; the no-order-unit claim is proved in the text."
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "total_checks": report["total_checks"],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
