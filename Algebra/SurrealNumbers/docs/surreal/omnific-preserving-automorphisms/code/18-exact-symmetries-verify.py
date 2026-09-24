#!/usr/bin/env python3
"""Exact finite checks for the accompanying surreal-symmetry manuscript.

This program checks finite two-level Hahn polynomials and rational models of
ordered group actions. It does NOT construct No, infinite Hahn sums, class
back-and-forth maps, or the transfinite equivariant cut-filling construction.
The general theorems are proved in article.tex, not established by these tests.

Python 3.10+; standard library only. Run: python3 verify.py
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from random import Random
import argparse
import json
from typing import Callable, TypeAlias

Inner: TypeAlias = tuple[tuple[Q, Q], ...]
Outer: TypeAlias = dict[Inner, Q]
OrderMap: TypeAlias = Callable[[Q], Q]
ZERO: Inner = ()
COUNTS: Counter[str] = Counter()
RNG = Random(20260923)


def check(category: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Failed check in category: {category}")
    COUNTS[category] += 1


def inner(terms) -> Inner:
    acc: dict[Q, Q] = {}
    for exponent, coefficient in terms:
        exponent, coefficient = Q(exponent), Q(coefficient)
        acc[exponent] = acc.get(exponent, Q(0)) + coefficient
    return tuple(sorted(((e, c) for e, c in acc.items() if c), reverse=True))


def iadd(a: Inner, b: Inner) -> Inner:
    return inner((*a, *b))


def ineg(a: Inner) -> Inner:
    return tuple((e, -c) for e, c in a)


def isign(a: Inner) -> int:
    return 0 if not a else (1 if a[0][1] > 0 else -1)


def lift_inner(a: Inner, phi: OrderMap) -> Inner:
    return inner((phi(e), c) for e, c in a)


def clean(a: Outer) -> Outer:
    return {e: c for e, c in a.items() if c}


def outer(terms) -> Outer:
    acc: Outer = {}
    for exponent, coefficient in terms:
        acc[exponent] = acc.get(exponent, Q(0)) + Q(coefficient)
    return clean(acc)


def add(a: Outer, b: Outer) -> Outer:
    return outer((*a.items(), *b.items()))


def mul(a: Outer, b: Outer) -> Outer:
    return outer((iadd(e, f), c*d) for e, c in a.items() for f, d in b.items())


def lift(a: Outer, phi: OrderMap) -> Outer:
    return outer((lift_inner(e, phi), c) for e, c in a.items())


def osign(a: Outer) -> int:
    if not a:
        return 0
    leading = next(iter(a))
    for exponent in a:
        if isign(iadd(exponent, ineg(leading))) > 0:
            leading = exponent
    return 1 if a[leading] > 0 else -1


def is_omnific(a: Outer) -> bool:
    return all(isign(e) >= 0 for e in a) and a.get(ZERO, Q(0)).denominator == 1


def twice_fixed(x: Q) -> Q:
    """Increasing rational bijection with fixed set {0,1}."""
    if x < 0:
        return 2*x
    if x > 1:
        return 2*x-1
    if x in (0, 1):
        return x
    return x/(2-x)


def twice_fixed_inverse(x: Q) -> Q:
    if x < 0:
        return x/2
    if x > 1:
        return (x+1)/2
    if x in (0, 1):
        return x
    return 2*x/(1+x)


def random_inner() -> Inner:
    return inner((Q(RNG.randrange(-5, 6), RNG.randrange(1, 4)),
                  Q(RNG.randrange(-3, 4), RNG.randrange(1, 4)))
                 for _ in range(RNG.randrange(0, 5)))


def random_outer(pool: list[Inner]) -> Outer:
    return outer((RNG.choice(pool), Q(RNG.randrange(-3, 4), RNG.randrange(1, 4)))
                 for _ in range(RNG.randrange(0, 7)))


def h_power(t: Q, k: int) -> Q:
    # h(t)=t/(2-t); h^k rescales t/(1-t) by 2^{-k}.
    scale = Q(2)**k
    return t / (scale + (1-scale)*t)


def b_power(x: Q, k: int) -> Q:
    n = x.numerator // x.denominator
    t = x-n
    return n + h_power(t, k if n % 2 == 0 else -k)


def kb_action(pair: tuple[int, int], x: Q) -> Q:
    m, n = pair  # b^m a^n
    return b_power(x+n, m)


def run() -> dict:
    COUNTS.clear()
    RNG.seed(20260923)
    maps = [
        ("translation", lambda x: x+1, lambda x: x-1, lambda x: False),
        ("dilation", lambda x: 2*x, lambda x: x/2, lambda x: x == 0),
        ("two_fixed_points", twice_fixed, twice_fixed_inverse,
         lambda x: x in (0, 1)),
    ]
    samples = sorted({Q(n, d) for n in range(-18, 19) for d in range(1, 7)})
    pool = [ZERO, inner([(0, 1)]), inner([(1, 1)])]
    pool += [random_inner() for _ in range(50)]
    unit = {ZERO: Q(1)}
    for name, phi, inverse, fixed in maps:
        for x in samples:
            check("order_map_inverse", inverse(phi(x)) == x and phi(inverse(x)) == x)
            check("order_map_fixed_set", (phi(x) == x) == fixed(x))
        for x, y in zip(samples, samples[1:]):
            check("order_map_monotonicity", phi(x) < phi(y))
        for iteration in range(180):
            a, b = random_outer(pool), random_outer(pool)
            fa, fb = lift(a, phi), lift(b, phi)
            check("double_lift_addition", lift(add(a, b), phi) == add(fa, fb))
            check("double_lift_multiplication", lift(mul(a, b), phi) == mul(fa, fb))
            check("double_lift_inverse", lift(fa, inverse) == a)
            check("unit", lift(unit, phi) == unit)
            check("order_sign", osign(fa) == osign(a))
            check("constant_coefficient", fa.get(ZERO, Q(0)) == a.get(ZERO, Q(0)))
            check("omnific_membership", is_omnific(a) == is_omnific(fa))
            support_fixed = all(fixed(index) for exponent in a for index, _ in exponent)
            check("two_level_fixed_support", (fa == a) == support_fixed)
            left = pool[1 + iteration % (len(pool)-1)]
            right = pool[-1 - iteration % (len(pool)-1)]
            check("inner_additivity", lift_inner(iadd(left, right), phi)
                  == iadd(lift_inner(left, phi), lift_inner(right, phi)))
            for _, psi, _, _ in maps:
                composition = lambda x, phi=phi, psi=psi: phi(psi(x))
                check("functoriality", lift(lift(a, psi), phi) == lift(a, composition))
        for _ in range(80):
            a = random_outer(pool)
            # A finite-support positive-exponent omnific sample, integer constant.
            positive = outer((e if isign(e) >= 0 else ineg(e), c)
                             for e, c in a.items() if e)
            positive[ZERO] = Q(RNG.randrange(-5, 6))
            positive = clean(positive)
            check("positive_omnific_samples", is_omnific(positive)
                  and is_omnific(lift(positive, phi)))
    for x in samples:
        check("klein_bottle_relation", b_power(x-1, 1)+1 == b_power(x, -1))
        for k in range(-5, 6):
            check("klein_bottle_inverse", b_power(b_power(x, k), -k) == x)
    for _ in range(700):
        p = (RNG.randrange(-5, 6), RNG.randrange(-5, 6))
        q = (RNG.randrange(-5, 6), RNG.randrange(-5, 6))
        m, n = p
        r, s = q
        product = (m + (1 if n % 2 == 0 else -1)*r, n+s)
        x = RNG.choice(samples)
        check("klein_bottle_group_law", kb_action(p, kb_action(q, x)) == kb_action(product, x))
        if p != (0, 0):
            witness = Q(0) if n else Q(1, 2)
            check("klein_bottle_normal_form_witness", kb_action(p, witness) != witness)
    for _ in range(300):
        s = set(RNG.sample(samples, RNG.randrange(0, 8)))
        t = set(RNG.sample(samples, RNG.randrange(0, 8)))
        a = random_outer(pool)
        support2 = {index for exponent in a for index, _ in exponent}
        check("support_hull_intersection", (support2 <= (s & t))
              == ((support2 <= s) and (support2 <= t)))
    return {
        "status": "PASS",
        "seed": 20260923,
        "arithmetic": "Exact fractions; no floating-point comparisons",
        "assertions": sum(COUNTS.values()),
        "by_category": dict(sorted(COUNTS.items())),
        "scope": "Finite two-level Hahn polynomials and rational ordered-action identities only",
        "not_checked": ["Infinite Hahn summability", "Class recursion", "Equivariant cut filling",
                        "No real-closedness", "Historical novelty", "Lean formalization"],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    report = run()
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
