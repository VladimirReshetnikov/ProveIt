#!/usr/bin/env python3
"""Exact finite regression checks for surreal_self_embeddings.tex.

These checks are NOT a verification of transfinite or proper-class theorems.
Python 3.10+; standard library only. Writes validation_results.json alongside
this script and prints the same JSON. Assertions raise immediately on failure.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random
from typing import Callable

SignWord = tuple[int, ...]
Poly = dict[F, F]  # finite formal sums: exponent -> coefficient
COUNTS: Counter[str] = Counter()


def check(group: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Regression failed in {group}")
    COUNTS[group] += 1


def words(max_length: int) -> list[SignWord]:
    return [s for n in range(max_length + 1) for s in product((-1, 1), repeat=n)]


def compare(s: SignWord, t: SignWord) -> int:
    for i in range(max(len(s), len(t))):
        a = s[i] if i < len(s) else 0
        b = t[i] if i < len(t) else 0
        if a != b:
            return 1 if a > b else -1
    return 0


def prefix(s: SignWord, t: SignWord) -> bool:
    return len(s) <= len(t) and t[:len(s)] == s


def block(s: SignWord, count: int) -> SignWord:
    if count < 1:
        raise ValueError("Block length must be positive")
    return tuple(a for sign in s for a in (sign,) * count)


def dyadic_value(s: SignWord) -> F:
    if not s:
        return F(0)
    run = 1
    while run < len(s) and s[run] == s[0]:
        run += 1
    value = F(s[0] * run)
    for power, sign in enumerate(s[run:], 1):
        value += F(sign, 2 ** power)
    return value


def clean(p: Poly) -> Poly:
    return {F(a): F(r) for a, r in p.items() if r}


def add(p: Poly, q: Poly) -> Poly:
    out = p.copy()
    for a, r in q.items():
        out[a] = out.get(a, F(0)) + r
    return clean(out)


def neg(p: Poly) -> Poly:
    return {a: -r for a, r in p.items()}


def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for a, r in p.items():
        for b, s in q.items():
            out[a + b] = out.get(a + b, F(0)) + r * s
    return clean(out)


def lift(p: Poly, f: Callable[[F], F]) -> Poly:
    out: Poly = {}
    for a, r in p.items():
        b = f(a)
        if b in out:
            raise ValueError("Exponent map is not injective on this support")
        out[b] = r
    return clean(out)


def compress(x: F) -> F:
    return x / (1 + abs(x))


def sigma_substitute_2t(p: Poly) -> Poly:
    """p(t) -> p(2t) for integer-exponent Laurent polynomials."""
    if any(a.denominator != 1 for a in p):
        raise ValueError("Substitution check requires integer exponents")
    return clean({a: r * F(2) ** int(a) for a, r in p.items()})


def evaluate(p: Poly, t: F) -> F:
    if t == 0 or any(a.denominator != 1 for a in p):
        raise ValueError("Need nonzero t and integer exponents")
    return sum((r * t ** int(a) for a, r in p.items()), F(0))


def run() -> dict[str, object]:
    all_words = words(6)
    p = (1, -1, 1)

    def localized(s: SignWord) -> SignWord:
        return p + block(s[len(p):], 2) if prefix(p, s) else s

    maps: list[tuple[str, Callable[[SignWord], SignWord]]] = [
        ("prefix_plus", lambda s: (1,) + s),
        ("prefix_mixed", lambda s: (1, -1) + s),
        ("block_two", lambda s: block(s, 2)),
        ("block_three", lambda s: block(s, 3)),
        ("localized_block", localized),
    ]
    for s in all_words:
        check("block_lengths", len(block(s, 3)) == 3 * len(s))
        check("local_fixed_short", len(s) > len(p) or localized(s) == s)
        check("local_fixed_ordinals", any(a < 0 for a in s) or localized(s) == s)
        for t in all_words:
            numeric = (dyadic_value(s) > dyadic_value(t)) - (dyadic_value(s) < dyadic_value(t))
            check("dyadic_lex_order", compare(s, t) == numeric)
            for name, fn in maps:
                check(name + "_order", compare(fn(s), fn(t)) == compare(s, t))
                check(name + "_prefix", prefix(fn(s), fn(t)) == prefix(s, t))

    check("explicit_nonadditivity", dyadic_value(block((1, -1), 2)) == F(5, 4))
    check("explicit_nonadditivity", 2 * dyadic_value(block((1, -1), 2)) != dyadic_value(block((1,), 2)))
    check("explicit_prefix_values", dyadic_value((1, -1)) == F(1, 2))

    grid = sorted({F(n, d) for n in range(-12, 13) for d in range(1, 9)})
    for x in grid:
        y = compress(x)
        check("compression_range", -1 < y < 1)
        check("compression_inverse", y / (1 - abs(y)) == x)
        check("compression_fixed", (y == x) == (x == 0))
        z = x
        for n in range(8):
            check("compression_iterates", z == x / (1 + n * abs(x)))
            z = compress(z)
    for a, b in zip(grid, grid[1:]):
        check("compression_order", compress(a) < compress(b))

    rng = random.Random(20261003)
    exponents = [F(n, d) for n in range(-5, 6) for d in (1, 2, 3)]
    polynomials = [clean({a: F(rng.randint(-5, 5), rng.randint(1, 4))
                          for a in rng.sample(exponents, rng.randint(0, 8))})
                   for _ in range(90)]
    for p1 in polynomials:
        check("finite_fixed_support", (lift(p1, compress) == p1) == all(a == 0 for a in p1))
        g = lambda a: a + 1
        check("finite_lift_composition", lift(lift(p1, g), compress) == lift(p1, lambda a: compress(g(a))))
        for p2 in polynomials:
            check("finite_lift_additivity", lift(add(p1, p2), compress) == add(lift(p1, compress), lift(p2, compress)))
            phi = lambda a: 2 * a
            check("finite_additive_exponent_multiplication",
                  lift(mul(p1, p2), phi) == mul(lift(p1, phi), lift(p2, phi)))
    mono = {F(1): F(1)}
    check("nonadditive_exponent_counterexample",
          lift(mul(mono, mono), compress) != mul(lift(mono, compress), lift(mono, compress)))

    laurents = [clean({F(a): F(rng.randint(-6, 6))
                       for a in rng.sample(range(-5, 6), rng.randint(0, 7))})
                for _ in range(50)]
    sig = sigma_substitute_2t
    delta = lambda p1: add(sig(p1), neg(p1))
    for p1 in laurents:
        for p2 in laurents:
            check("twisted_displacement_identity",
                  delta(mul(p1, p2)) == add(mul(sig(p1), delta(p2)), mul(p2, delta(p1))))
    a_poly = {F(1): F(1)}
    check("untwisted_identity_counterexample",
          delta(mul(a_poly, a_poly)) != add(mul(a_poly, delta(a_poly)), mul(a_poly, delta(a_poly))))
    for B in (F(1, 3), F(1), F(10), F(100)):
        # On positive t, a=t, sigma(a)=2t, d=t, so the exact probe is 4B+2B/t.
        probe = {F(0): 4 * B, F(-1): 2 * B}
        for t in (F(1), F(2), F(10)):
            check("two_probe_amplification",
                  max(abs(evaluate(delta(probe), t)),
                      abs(evaluate(delta(mul(a_poly, probe)), t))) > B)

    return {
        "status": "PASS",
        "seed": 20261003,
        "total_assertions": sum(COUNTS.values()),
        "assertions_by_group": dict(sorted(COUNTS.items())),
        "scope": "Exact finite signs, rational compression, finite Hahn-style supports, and Laurent-polynomial algebra.",
        "limitations": [
            "Not a Lean or other proof-assistant verification.",
            "Does not verify transfinite reverse well-orders or arbitrary infinite summable families.",
            "Does not verify proper-class constructions, elementarity, or large-cardinal hypotheses.",
            "The double-lift and infinite-support theorems rely on the written proofs in the article."
        ]
    }


if __name__ == "__main__":
    result = run()
    text = json.dumps(result, indent=2) + "\n"
    (Path(__file__).resolve().parent / "validation_results.json").write_text(text, encoding="utf-8")
    print(text, end="")
