#!/usr/bin/env python3
"""Exact finite checks accompanying Support-Bounded Surreal Fields.

These checks test finite rational normal forms and identities only. They do
not verify cardinal arithmetic, class arguments, saturation, or novelty.
Uses Python 3 standard library; no floating point arithmetic.
"""
from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Mapping

Series = dict[Fraction, Fraction]
COUNTS: Counter[str] = Counter()


def clean(x: Mapping[Fraction, Fraction]) -> Series:
    return {Fraction(g): Fraction(c) for g, c in x.items() if c}


def add(x: Series, y: Series) -> Series:
    out = dict(x)
    for g, c in y.items():
        out[g] = out.get(g, Fraction(0)) + c
    return clean(out)


def scale(x: Series, c: Fraction) -> Series:
    return clean({g: c * a for g, a in x.items()})


def sub(x: Series, y: Series) -> Series:
    return add(x, scale(y, Fraction(-1)))


def mul(x: Series, y: Series) -> Series:
    out: Series = {}
    for g, a in x.items():
        for h, b in y.items():
            out[g + h] = out.get(g + h, Fraction(0)) + a * b
    return clean(out)


def shift(x: Series, g: Fraction) -> Series:
    return clean({h + g: c for h, c in x.items()})


def sign(x: Series) -> int:
    if not x:
        return 0
    c = x[max(x)]
    return 1 if c > 0 else -1


def cmp(x: Series, y: Series) -> int:
    return sign(sub(x, y))


def prefix(x: Series, n: int) -> Series:
    return {g: x[g] for g in sorted(x, reverse=True)[:n]}


def ball_contains(x: Series, center: Series, radius: Fraction) -> bool:
    difference = sub(x, center)
    return not difference or -max(difference) >= radius


def check(group: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Failed finite check in {group}")
    COUNTS[group] += 1


def finite_series(exponents: list[Fraction], coefficients: list[Fraction]):
    for row in itertools.product(coefficients, repeat=len(exponents)):
        yield clean(dict(zip(exponents, row)))


def run_checks() -> dict:
    q = Fraction
    one: Series = {q(0): q(1)}

    # First exponent outside S: inserted exponents and missing coefficients
    # are compared using a common exponent grid, not term positions.
    grid = [q(3), q(2), q(1), q(0), q(-1)]
    values = [q(-1), q(0), q(1)]
    allowed = {q(3), q(1), q(-1)}
    candidates = list(finite_series(sorted(allowed), values))
    for y in finite_series(grid, values):
        outside = set(y) - allowed
        if not outside:
            continue
        gamma = max(outside)
        z = {g: c for g, c in y.items() if g >= gamma}
        check("separator_support", set(z) <= allowed | {gamma})
        for a in candidates:
            check("first_outside_comparison", cmp(a, y) == cmp(a, z))

    # All signs of nonzero coefficients, including negative prefix terms.
    p_grid = [q(5), q(3), q(1), q(-1), q(-3)]
    for coefficients in itertools.product([q(-2), q(-1), q(1), q(2)], repeat=5):
        p = dict(zip(p_grid, coefficients))
        for index, g in enumerate(p_grid):
            t = prefix(p, index)
            margin = abs(p[g]) + 1
            lower = add(t, {g: -margin})
            upper = add(t, {g: margin})
            check("prefix_brackets", cmp(lower, p) < 0 < cmp(upper, p))
            # Altering an earlier coefficient is detected before this bracket.
            if index:
                earlier = p_grid[index - 1]
                below = add(prefix(p, index), {earlier: q(-1)})
                above = add(prefix(p, index), {earlier: q(1)})
                check("later_bracket_separation", cmp(below, lower) < 0)
                check("later_bracket_separation", cmp(upper, above) < 0)

    # Boundary convention B(s_beta,beta): the coefficient at -beta is NOT fixed.
    for length in range(1, 61):
        full = {q(-n): q(1) for n in range(length)}
        for beta in range(length + 1):
            center = {q(-n): q(1) for n in range(beta)}
            check("nested_balls", ball_contains(full, center, q(beta)))
            boundary = add(center, {q(-beta): q(7)})
            check("closed_ball_boundary_allowed", ball_contains(boundary, center, q(beta)))
            if beta:
                bad = add(center, {q(1 - beta): q(1)})
                check("earlier_coefficient_forbidden", not ball_contains(bad, center, q(beta)))

    # Floor formula: real integer boundary plus either sign of infinitesimal.
    for n in range(-12, 13):
        for residue in [q(0), q(1, 7), q(2, 3)]:
            for eps in [q(-3), q(-1), q(0), q(1), q(3)]:
                x = clean({q(4): q(2), q(2): q(-3), q(0): q(n) + residue, q(-1): eps})
                ordinary_floor = n - (1 if residue == 0 and eps < 0 else 0)
                a = clean({q(4): q(2), q(2): q(-3), q(0): q(ordinary_floor)})
                check("omnific_floor", cmp(a, x) <= 0 and cmp(x, add(a, one)) < 0)

    # Finite geometric inverse identity, not an assertion of infinite convergence.
    for eta in [{q(-1): q(1)}, {q(-1): q(2), q(-3): q(-1)}, {q(-2): q(-3), q(-5): q(2)}]:
        for n in range(1, 21):
            power = dict(one)
            total: Series = {}
            for j in range(n):
                total = add(total, scale(power, q((-1) ** j)))
                power = mul(power, eta)
            left = mul(add(one, eta), total)
            right = add(one, scale(power, q((-1) ** (n - 1))))
            check("geometric_identity", left == right)

    # Constant extraction is multiplicative for nonnegative-growth support.
    positive = [q(0), q(1), q(2)]
    samples = list(finite_series(positive, [q(-2), q(0), q(3)]))
    for a, b in itertools.product(samples, repeat=2):
        c0a = a.get(q(0), q(0))
        c0b = b.get(q(0), q(0))
        check("constant_term_product", mul(a, b).get(q(0), q(0)) == c0a * c0b)

    # Scaled collision identity using nonzero monomial e-f with exact inverse.
    for d in range(1, 13):
        for h in [q(-1, 3), q(0), q(1, 3)]:
            for coefficient in [q(-3), q(-1), q(1, 2), q(2)]:
                left = {q(d) + h: coefficient}
                right = {q(d) - h: 1 / coefficient}
                check("scaled_collision", mul(left, right) == {q(2 * d): q(1)})
                check("shifted_positive_support", min(left) > 0 and min(right) > 0)

    # Support shift and a finite analogue of the logarithmic escape preparation.
    for length in range(1, 101):
        s = {q(-n): q(1) for n in range(length)}
        p = shift(s, q(length))
        check("positive_shift", len(p) == length and min(p) > 0)
        for cut in range(length + 1):
            check("prefix_reconstruction", add(prefix(s, cut), {g: c for g, c in s.items() if g not in prefix(s, cut)}) == s)

    return {
        "status": "passed",
        "arithmetic": "exact Fraction arithmetic; Python standard library",
        "total_checks": sum(COUNTS.values()),
        "counts": dict(sorted(COUNTS.items())),
        "scope": "Finite identities and boundary conventions only.",
        "not_verified": [
            "cardinal and cofinality arguments", "infinite Hahn summability",
            "class constructions and class back-and-forth", "saturation theorems",
            "nonexistence of surjective exponential", "bibliographic novelty",
            "Lean formalization"
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    result = run_checks()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
