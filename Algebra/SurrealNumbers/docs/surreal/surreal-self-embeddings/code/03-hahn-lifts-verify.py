#!/usr/bin/env python3
"""Exact finite regression checks for the accompanying surreal-embedding article.

These checks do NOT prove the transfinite or proper-class theorems. They detect
transcription errors in finite sign combinatorics, rational branch formulas,
finite two-level Hahn relabeling, and binomial unit identities.
Only the Python standard library is required (Python 3.10+).
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from functools import total_ordering
from itertools import product
import json
from pathlib import Path
import random
from typing import Callable, Iterable

COUNTS: Counter[str] = Counter()


def check(condition: bool, group: str) -> None:
    COUNTS[group] += 1
    if not condition:
        raise AssertionError(f"Failed check {COUNTS[group]} in {group}")


def sign_compare(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    for k in range(max(len(a), len(b))):
        x = a[k] if k < len(a) else 0
        y = b[k] if k < len(b) else 0
        if x != y:
            return (x > y) - (x < y)
    return 0


def prefix(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return len(a) <= len(b) and b[:len(a)] == a


def repeated(a: tuple[int, ...], m: int) -> tuple[int, ...]:
    return tuple(s for s in a for _ in range(m))


def finite_value(a: tuple[int, ...]) -> F:
    if not a:
        return F(0)
    value, step, changed = F(0), F(1), False
    for k, s in enumerate(a):
        if k > 0 and (changed or s != a[0]):
            step /= 2
            changed = True
        value += s * step
    return value


def fminus(a: F) -> F:
    return a / (1 - a) if a < 0 else a


def flower(a: F, beta: F) -> F:
    d = a - beta
    return beta + d / (1 - d) if a < beta else a


def lower_inverse(y: F, beta: F) -> F:
    if y <= beta - 1:
        raise ValueError("Not in the lower-tail map's range")
    d = y - beta
    return beta + d / (1 + d) if y < beta else y


def fupper(a: F, gamma: F) -> F:
    d = a - gamma
    return gamma + d / (1 + d) if a > gamma else a


def upper_inverse(y: F, gamma: F) -> F:
    if y >= gamma + 1:
        raise ValueError("Not in the upper-tail map's range")
    d = y - gamma
    return gamma + d / (1 - d) if y > gamma else y


@total_ordering
@dataclass(frozen=True)
class Exponent:
    """A finite inner Hahn series with rational exponents and coefficients.

    This is a finite symbolic surrogate for a surreal used as an OUTER
    exponent. It is not a general implementation of surreal arithmetic.
    """
    terms: tuple[tuple[F, F], ...]

    @classmethod
    def make(cls, terms: Iterable[tuple[F, F]]) -> Exponent:
        d: dict[F, F] = {}
        for a, c in terms:
            d[a] = d.get(a, F(0)) + c
        return cls(tuple(sorted(((a, c) for a, c in d.items() if c), reverse=True)))

    def __add__(self, other: Exponent) -> Exponent:
        return Exponent.make(self.terms + other.terms)

    def __neg__(self) -> Exponent:
        return Exponent.make((a, -c) for a, c in self.terms)

    def __sub__(self, other: Exponent) -> Exponent:
        return self + (-other)

    def __lt__(self, other: Exponent) -> bool:
        diff = self - other
        return bool(diff.terms) and diff.terms[0][1] < 0

    def relabel(self, f: Callable[[F], F]) -> Exponent:
        return Exponent.make((f(a), c) for a, c in self.terms)


Series = dict[Exponent, F]
ZERO_EXP = Exponent(())
ONE_SERIES: Series = {ZERO_EXP: F(1)}


def clean(d: Series) -> Series:
    return {a: c for a, c in d.items() if c}


def series_add(x: Series, y: Series) -> Series:
    d = dict(x)
    for a, c in y.items():
        d[a] = d.get(a, F(0)) + c
    return clean(d)


def series_mul(x: Series, y: Series) -> Series:
    d: Series = {}
    for a, r in x.items():
        for b, s in y.items():
            k = a + b
            d[k] = d.get(k, F(0)) + r * s
    return clean(d)


def double_lift(x: Series, f: Callable[[F], F]) -> Series:
    d: Series = {}
    for a, r in x.items():
        k = a.relabel(f)
        d[k] = d.get(k, F(0)) + r
    return clean(d)


def series_compare(x: Series, y: Series) -> int:
    d = series_add(x, {a: -c for a, c in y.items()})
    if not d:
        return 0
    c = d[max(d)]
    return (c > 0) - (c < 0)


def binomial(r: F, n: int) -> F:
    b = F(1)
    for k in range(n):
        b *= (r - k) / (k + 1)
    return b


def run() -> dict[str, object]:
    words = [tuple(s) for n in range(7) for s in product((-1, 1), repeat=n)]
    for a in words:
        for b in words:
            expected = sign_compare(a, b)
            check(expected == ((finite_value(a) > finite_value(b)) -
                               (finite_value(a) < finite_value(b))), "finite sign order")
            for m in (2, 3):
                da, db = repeated(a, m), repeated(b, m)
                check(sign_compare(da, db) == expected, "sign repetition order")
                check(prefix(da, db) == prefix(a, b), "sign repetition prefix")
            for p in ((), (1,), (-1, 1, -1)):
                check(sign_compare(p + a, p + b) == expected, "prefix copies order")
                check(prefix(p + a, p + b) == prefix(a, b), "prefix copies prefix")
    check(finite_value(repeated((1, -1), 2)) == F(5, 4), "dyadic witnesses")
    check(finite_value(repeated((1,), 2)) == 2, "dyadic witnesses")

    grid = sorted({F(p, q) for p in range(-36, 37) for q in range(1, 7)})
    for beta in (F(-7), F(-1), F(-1, 3)):
        vals = [flower(x, beta) for x in grid]
        for x, y in zip(grid, vals):
            check(y > beta - 1, "lower rational range")
            check(lower_inverse(y, beta) == x, "lower rational inverse")
        for a, b in zip(vals, vals[1:]):
            check(a < b, "lower rational monotonicity")
    for gamma in (F(1, 4), F(2), F(9)):
        vals = [fupper(x, gamma) for x in grid]
        for x, y in zip(grid, vals):
            check(y < gamma + 1, "upper rational range")
            check(upper_inverse(y, gamma) == x, "upper rational inverse")
        for a, b in zip(vals, vals[1:]):
            check(a < b, "upper rational monotonicity")
    for a in grid:
        x = a
        for n in range(1, 13):
            x = fminus(x)
            check(x == (a / (1 - n*a) if a < 0 else a), "rational iterate formula")
            check(x > F(-1, n), "rational iterate range")

    rng = random.Random(20261003)
    inner_exps = [F(p, q) for p in range(-5, 6) for q in (1, 2)]

    def random_exp() -> Exponent:
        return Exponent.make((rng.choice(inner_exps), F(rng.randint(-4, 4), 2))
                             for _ in range(rng.randrange(4)))

    def random_series() -> Series:
        d: Series = {}
        for _ in range(rng.randrange(1, 5)):
            a = random_exp()
            d[a] = d.get(a, F(0)) + F(rng.randint(-4, 4), 2)
        return clean(d)

    maps: list[Callable[[F], F]] = [fminus, lambda a: a+1,
                                  lambda a: fupper(a, F(2))]
    for _ in range(150):
        x, y = random_series(), random_series()
        for f in maps:
            check(double_lift(series_add(x, y), f) ==
                  series_add(double_lift(x, f), double_lift(y, f)), "double lift addition")
            check(double_lift(series_mul(x, y), f) ==
                  series_mul(double_lift(x, f), double_lift(y, f)), "double lift multiplication")
            check(series_compare(x, y) ==
                  series_compare(double_lift(x, f), double_lift(y, f)), "double lift order")
            check(double_lift(ONE_SERIES, f) == ONE_SERIES, "double lift unit")
            for g in maps:
                check(double_lift(double_lift(x, g), f) ==
                      double_lift(x, lambda a: f(g(a))), "double lift composition")
    witness_exp = Exponent.make([(F(-1), F(1))])
    expected_exp = Exponent.make([(F(-1, 2), F(1))])
    check(double_lift({witness_exp: F(1)}, fminus) == {expected_exp: F(1)},
          "explicit moved monomial")

    for r in [F(p, q) for p in range(-4, 5) for q in (1, 2, 3)]:
        for s in [F(p, 2) for p in range(-4, 5)]:
            for n in range(11):
                check(sum((binomial(r, k)*binomial(s, n-k) for k in range(n+1)), F(0))
                      == binomial(r+s, n), "binomial unit multiplication")
        for n in range(11):
            check(sum((binomial(r, k)*binomial(-r, n-k) for k in range(n+1)), F(0))
                  == (1 if n == 0 else 0), "binomial unit inverse")

    for _ in range(500):
        a, sa = F(rng.randint(-10, 10), 3), F(rng.randint(-10, 10), 2)
        if a == sa:
            continue
        B = F(rng.randint(1, 20), 3)
        da = sa-a
        b = 2*B*(1+abs(sa))/abs(da)
        db = F(rng.randint(-20, 20), 7)
        dab = sa*db + b*da
        check(max(abs(db), abs(dab)) > B, "finite displacement probe")

    return {"status": "PASS", "seed": 20261003,
            "checks": dict(sorted(COUNTS.items())),
            "total_checks": sum(COUNTS.values()),
            "scope": "Finite exact regression tests only; not a transfinite or Lean proof."}


if __name__ == "__main__":
    result = run()
    print(json.dumps(result, indent=2))
    Path(__file__).with_name("verification.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
