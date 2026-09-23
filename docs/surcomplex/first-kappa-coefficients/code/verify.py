#!/usr/bin/env python3
"""Exact finite checks for article.tex (Python 3.10+, standard library only).

These are tests of finite algebraic mechanisms, NOT verification of transfinite
supports, cardinal arithmetic, first-order types, or publication priority.
A finite support cutoff is not treated as a field.
"""
from __future__ import annotations

import json
import random
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Mapping

Exponent = tuple[int, int]  # lexicographic order; first coordinate dominates
Value = Exponent | None    # None denotes +infinity
Series = dict[Exponent, Fraction]
ZERO: Exponent = (0, 0)
COUNTS: Counter[str] = Counter()
RNG = random.Random(20260922)


def check(condition: bool, family: str) -> None:
    if not condition:
        raise AssertionError(f"Failure in {family}; preceding counts: {dict(COUNTS)}")
    COUNTS[family] += 1


def clean(a: Mapping[Exponent, Fraction | int]) -> Series:
    return {g: Fraction(c) for g, c in a.items() if c}


def add(a: Series, b: Series) -> Series:
    result = dict(a)
    for g, c in b.items():
        result[g] = result.get(g, Fraction(0)) + c
        if not result[g]:
            del result[g]
    return result


def scale(a: Series, c: Fraction | int) -> Series:
    return clean({g: c * x for g, x in a.items()})


def sub(a: Series, b: Series) -> Series:
    return add(a, scale(b, -1))


def shift(g: Exponent, h: Exponent) -> Exponent:
    return (g[0] + h[0], g[1] + h[1])


def negate(g: Exponent) -> Exponent:
    return (-g[0], -g[1])


def mul(a: Series, b: Series) -> Series:
    out: Series = {}
    for g, c in a.items():
        for h, d in b.items():
            p = shift(g, h)
            out[p] = out.get(p, Fraction(0)) + c * d
    return clean(out)


def value(a: Series) -> Value:
    return min(a) if a else None


def lc(a: Series) -> Fraction:
    return a[min(a)] if a else Fraction(0)


def le(a: Value, b: Value) -> bool:
    """a <= b with None interpreted as infinity."""
    if b is None:
        return True
    return a is not None and a <= b


def lt(a: Value, b: Value) -> bool:
    return a != b and le(a, b)


def trunc(a: Series, g: Exponent) -> Series:
    return {h: c for h, c in a.items() if h < g}


def random_series(max_terms: int = 5) -> Series:
    out: Series = {}
    for _ in range(RNG.randrange(max_terms + 1)):
        g = (RNG.randrange(-2, 3), RNG.randrange(-8, 9))
        c = Fraction(RNG.randrange(-5, 6), RNG.randrange(1, 5))
        out[g] = out.get(g, Fraction(0)) + c
    return clean(out)


def test_hahn_identities() -> None:
    for _ in range(450):
        a, b, c = random_series(), random_series(), random_series()
        g = (RNG.randrange(-3, 4), RNG.randrange(-9, 10))
        check(le(g, value(sub(a, b))) == (trunc(a, g) == trunc(b, g)),
              "first_disagreement")
        check(add(a, b) == add(b, a), "addition")
        check(mul(a, add(b, c)) == add(mul(a, b), mul(a, c)), "distributivity")
        if a and b:
            va, vb = value(a), value(b)
            assert va is not None and vb is not None
            check(value(mul(a, b)) == shift(va, vb), "multiplicative_value")
            check(lc(mul(a, b)) == lc(a) * lc(b), "multiplicative_leading_coefficient")
            if va != vb:
                check(value(add(a, b)) == min(va, vb), "unequal_value_sum")


def test_prefix_probes() -> None:
    # A finite surrogate for the first-disagreement argument only.
    n = 7
    prefix = clean({(0, j): Fraction(j + 1, j + 2) for j in range(n)})
    x = add(prefix, clean({(1, 0): 2}))
    y = add(prefix, clean({(2, -10): -3, (3, 4): 7}))
    check(lt((0, n - 1), value(sub(x, y))), "high_tail")
    for _ in range(400):
        roots = [random_series(n - 1) for _ in range(RNG.randrange(1, 5))]
        px = clean({ZERO: 1})
        py = clean({ZERO: 1})
        for a in roots:
            xa, ya = sub(x, a), sub(y, a)
            check(le(value(xa), (0, n - 1)), "bounded_first_disagreement")
            check(value(xa) == value(ya), "linear_value_invariance")
            check(lc(xa) == lc(ya), "linear_leading_invariance")
            px, py = mul(px, xa), mul(py, ya)
        check(value(px) == value(py), "factored_polynomial_value")
        check(lc(px) == lc(py), "factored_polynomial_leading_coefficient")


def test_ball_gluing() -> None:
    x = clean({(0, j): Fraction((-1) ** j, j + 1) for j in range(12)})
    radii = [(0, j) for j in (2, 4, 7, 10)]
    centers = [add(trunc(x, r), clean({shift(r, (1, 0)): 7})) for r in radii]
    # Each center may differ above its prescribed radius.
    f: Series = {}
    for a, r in zip(centers, radii):
        for g, c in a.items():
            if g < r:
                if g in f:
                    check(f[g] == c, "glue_consistency")
                f[g] = c
    for i, (a, r) in enumerate(zip(centers, radii)):
        check(le(r, value(sub(f, a))), "glued_ball_membership")
        for j in range(i + 1, len(radii)):
            check(le(r, value(sub(a, centers[j]))), "nested_ball_centers")


def test_projection_loss() -> None:
    for _ in range(1800):
        x, c, d = random_series(), random_series(), random_series()
        rc, rd = value(sub(x, c)), value(sub(x, d))
        if rc is None or rd is None:
            continue
        # All lexicographically nonnegative losses, including high-rank ones.
        delta = RNG.choice([(0, 0), (0, 1), (0, 7), (1, -100), (2, 0)])
        local_bound = le(shift(rd, negate(delta)), value(sub(c, d)))
        cut_bound = le(rd, shift(rc, delta))
        check(local_bound == cut_bound, "projection_loss_equivalence")
        if rc != rd:
            check(value(sub(c, d)) == min(rc, rd), "projection_trichotomy")
        else:
            check(le(rc, value(sub(c, d))), "projection_equal_value_case")


def main() -> None:
    test_hahn_identities()
    test_prefix_probes()
    test_ball_gluing()
    test_projection_loss()
    result = {
        "seed": 20260922,
        "arithmetic": "exact fractions; finite supports in lexicographically ordered Z^2",
        "status": "all assertions passed",
        "total_assertions": sum(COUNTS.values()),
        "families": dict(sorted(COUNTS.items())),
        "scope": "finite local identities only; not a transfinite or formal proof",
    }
    path = Path(__file__).resolve().with_name("verification.json")
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
