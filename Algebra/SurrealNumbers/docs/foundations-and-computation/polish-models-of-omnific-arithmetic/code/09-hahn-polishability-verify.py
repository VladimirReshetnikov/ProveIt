#!/usr/bin/env python3
"""Exact finite regression checks for article.tex.

Python 3.10+; standard library only. This is not a verification of the
infinite-series, category, descriptive-complexity, or real-closedness proofs.
All finite exponents and coefficients use fractions.Fraction.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from typing import Mapping

Poly = dict[Q, Q]
COUNTS: Counter[str] = Counter()
ONE: Poly = {Q(0): Q(1)}


def check(name: str, assertion: bool) -> None:
    """Count a passed assertion, or fail with its test-family name."""
    if not assertion:
        raise AssertionError(f"Regression failure: {name}")
    COUNTS[name] += 1


def clean(p: Mapping[Q, Q]) -> Poly:
    return {Q(q): Q(a) for q, a in p.items() if a != 0}


def add(p: Poly, r: Poly) -> Poly:
    out = dict(p)
    for q, a in r.items():
        out[q] = out.get(q, Q(0)) + a
    return clean(out)


def scale(p: Poly, a: Q) -> Poly:
    return clean({q: a * c for q, c in p.items()})


def sub(p: Poly, r: Poly) -> Poly:
    return add(p, scale(r, Q(-1)))


def shift(p: Poly, q: Q) -> Poly:
    return {s + q: c for s, c in p.items()}


def mul(p: Poly, r: Poly) -> Poly:
    out: Poly = {}
    for s, a in p.items():
        for t, b in r.items():
            out[s + t] = out.get(s + t, Q(0)) + a * b
    return clean(out)


def trunc(p: Poly, cutoff: Q) -> Poly:
    return {q: a for q, a in p.items() if q <= cutoff}


def valuation(p: Poly) -> Q | None:
    return min(p) if p else None  # None represents +infinity.


def sign(p: Poly) -> int:
    if not p:
        return 0
    a = p[min(p)]
    return 1 if a > 0 else -1


def integer_part(p: Poly) -> Poly:
    """Omnific floor of a finite rational-coefficient polynomial."""
    result = {q: a for q, a in p.items() if q < 0}
    c = p.get(Q(0), Q(0))
    u = {q: a for q, a in p.items() if q > 0}
    n = math.floor(c)
    if c.denominator == 1 and sign(u) < 0:
        n -= 1
    if n:
        result[Q(0)] = Q(n)
    return clean(result)


def inverse_to(p: Poly, cutoff: Q) -> Poly:
    """Exact coefficients of 1/p through cutoff, using a geometric expansion.

    This handles a nonzero finite input polynomial. The returned finite
    dictionary is a truncation of its potentially infinite inverse.
    """
    if not p:
        raise ZeroDivisionError("The zero series has no inverse.")
    q = min(p)
    a = p[q]
    h = sub(scale(shift(p, -q), 1 / a), ONE)
    bound = cutoff + q
    if bound < 0:
        return {}
    if not h:
        return trunc({-q: 1 / a}, cutoff)
    delta = min(h)
    if delta <= 0:
        raise ValueError("Normalization did not produce positive valuation.")
    power = dict(ONE)
    total = dict(ONE)
    for _ in range(math.floor(bound / delta)):
        power = trunc(mul(power, scale(h, Q(-1))), bound)
        total = add(total, power)
    return trunc(scale(shift(total, -q), 1 / a), cutoff)


def random_poly(rng: random.Random, terms: int = 5) -> Poly:
    p: Poly = {}
    for _ in range(terms):
        q = Q(rng.randint(-12, 12), rng.randint(1, 6))
        a = Q(rng.randint(-9, 9), rng.randint(1, 7))
        p[q] = p.get(q, Q(0)) + a
    return clean(p)


def run() -> dict[str, object]:
    rng = random.Random(20261003)
    for _ in range(400):
        p, r, s = (random_poly(rng, 4) for _ in range(3))
        check("addition_commutes", add(p, r) == add(r, p))
        check("addition_associates", add(add(p, r), s) == add(p, add(r, s)))
        check("multiplication_commutes", mul(p, r) == mul(r, p))
        check("multiplication_associates", mul(mul(p, r), s) == mul(p, mul(r, s)))
        check("distributivity", mul(p, add(r, s)) == add(mul(p, r), mul(p, s)))
        if p and r:
            check("product_valuation", valuation(mul(p, r)) == min(p) + min(r))
        summed = add(p, r)
        if p and r and summed:
            check("sum_valuation_bound", min(summed) >= min(min(p), min(r)))

    for _ in range(1200):
        f = random_poly(rng, 8)
        a = integer_part(f)
        check("floor_lower_bound", sign(sub(f, a)) >= 0)
        check("floor_strict_upper_bound", sign(sub(add(a, ONE), f)) > 0)
        check("floor_idempotent", integer_part(a) == a)
        check("integer_part_constant_integral", a.get(Q(0), Q(0)).denominator == 1)
        check("integer_part_no_positive_exponents", all(q <= 0 for q in a))
        i = integer_part(random_poly(rng, 4))
        check("floor_translation", integer_part(add(f, i)) == add(a, i))
        n = max(0, math.ceil(max(f))) if f else 0
        check("floor_truncation_eventually_exact", integer_part(trunc(f, Q(n))) == a)

    for _ in range(120):
        q = rng.choice([Q(-2), Q(-1, 2), Q(0), Q(1, 3), Q(2)])
        a = rng.choice([Q(-3), Q(-1), Q(1, 2), Q(1), Q(5, 3)])
        h = clean({Q(1, 2): Q(rng.randint(-2, 2)),
                   Q(1): Q(rng.randint(-2, 2)),
                   Q(3, 2): Q(rng.randint(-2, 2))})
        f = scale(shift(add(ONE, h), q), a)
        cutoff = Q(4)
        inv = inverse_to(f, cutoff)
        check("truncated_inverse", trunc(mul(f, inv), cutoff + q) == ONE)

    caught = False
    try:
        inverse_to({}, Q(4))
    except ZeroDivisionError:
        caught = True
    check("inverse_zero_guard", caught)

    for _ in range(100):
        a = integer_part(random_poly(rng, 6))
        for n in range(1, 16):
            left = sub(a, {Q(n): Q(1)})
            right = add(a, {Q(n): Q(1)})
            check("floor_negative_boundary", integer_part(left) == sub(a, ONE))
            check("floor_positive_boundary", integer_part(right) == a)
            check("boundary_difference_valuation", valuation(sub(left, a)) == n)

    gammas = [Q(1) - Q(1, m + 2) for m in range(6)]
    check("bounded_hahn_exponents", all(0 < x < 1 for x in gammas))
    check("increasing_hahn_exponents", all(x < y for x, y in zip(gammas, gammas[1:])))
    family = [{gammas[m]: Q(bit) for m, bit in enumerate(bits) if bit}
              for bits in itertools.product((0, 1), repeat=6)]
    for p, r in itertools.combinations(family, 2):
        difference = sub(p, r)
        absolute = scale(difference, Q(sign(difference)))
        check("binary_centers_separated", sign(sub(absolute, {Q(1): Q(2)})) > 0)
        check("binary_difference_below_cutoff", min(difference) < 1)

    rows = [Q(n + 1) - Q(1, m + 2) for n in range(50) for m in range(50)]
    check("row_code_injective", len(set(rows)) == len(rows))
    for n in range(50):
        exponents = [Q(n + 1) - Q(1, m + 2) for m in range(50)]
        check("row_code_confined", all(n < q < n + 1 for q in exponents))
        check("row_code_increasing", all(a < b for a, b in zip(exponents, exponents[1:])))

    witness = [Q(n) + Q(1, n) for n in range(2, 151)]
    for n, q in enumerate(witness, start=2):
        check("unbounded_denominator_exact", q.denominator == n)
    check("levi_civita_witness_increasing", all(a < b for a, b in zip(witness, witness[1:])))
    for r in range(1, 11):
        factorial = math.factorial(r)
        check("finite_puiseux_stage_escape", any(factorial % q.denominator for q in witness))

    return {
        "status": "passed",
        "seed": 20261003,
        "arithmetic": "Exact fractions.Fraction coefficients and exponents",
        "assertions_passed": sum(COUNTS.values()),
        "test_families": dict(sorted(COUNTS.items())),
        "scope": "Finite regression checks for the displayed examples and algorithms only",
        "not_verified": [
            "Baire-category or automatic-continuity theorems",
            "Quantification over all admissible Polish topologies",
            "Infinite support, Borel-completeness, and real-closedness proofs",
            "Lean or Rocq kernel verification",
            "Global publication priority"
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
