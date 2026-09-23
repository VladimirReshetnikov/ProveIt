#!/usr/bin/env python3
"""Exact finite tests accompanying surreal_embeddings.tex.

This checks finite/truncated algebra, NOT the infinite-support or proper-class
proofs. Coefficients are Laurent polynomials in a transcendental symbol b over Q.
The image model is Q[b,b^-1][T^Q][u]/(u^(N+1)); (q,n) is read lexicographically.
No external Python packages or network access are required.
"""
from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction as F
from pathlib import Path
from typing import Callable

# Keys are (outer exponent of T, degree of u, Laurent exponent of b).
Key = tuple[F, int, int]
Poly = dict[Key, F]
COUNTS: dict[str, int] = {}


def check(condition: bool, category: str, message: str) -> None:
    if not condition:
        raise AssertionError(f"{category}: {message}")
    COUNTS[category] = COUNTS.get(category, 0) + 1


def clean(p: Poly) -> Poly:
    return {key: value for key, value in p.items() if value}


def add(p: Poly, q: Poly) -> Poly:
    out = dict(p)
    for key, value in q.items():
        out[key] = out.get(key, F(0)) + value
    return clean(out)


def mul(p: Poly, q: Poly, cutoff: int) -> Poly:
    out: Poly = {}
    for (g, n, k), a in p.items():
        for (h, m, ell), b in q.items():
            if n + m <= cutoff:
                key = (g + h, n + m, k + ell)
                out[key] = out.get(key, F(0)) + a * b
    return clean(out)


def binomial_integer(k: int, n: int) -> F:
    """Generalized binomial coefficient, allowing negative integer k."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    value = F(1)
    for j in range(n):
        value *= F(k - j, j + 1)
    return value


def taylor(p: Poly, cutoff: int, parameter: F = F(1)) -> Poly:
    """Substitute b -> b + parameter*u, exactly modulo u^(cutoff+1)."""
    out: Poly = {}
    for (g, n, k), a in p.items():
        for m in range(cutoff - n + 1):
            value = a * binomial_integer(k, m) * parameter**m
            if value:
                key = (g, n + m, k - m)
                out[key] = out.get(key, F(0)) + value
    return clean(out)


def random_poly(rng: random.Random, cutoff: int, source: bool = False) -> Poly:
    out: Poly = {}
    for _ in range(rng.randrange(1, 7)):
        key = (F(rng.randrange(-6, 7), rng.randrange(1, 4)),
               0 if source else rng.randrange(cutoff + 1),
               rng.randrange(-4, 5))
        out[key] = out.get(key, F(0)) + F(rng.randrange(-4, 5),
                                       rng.randrange(1, 5))
    return clean(out)


def source_integer_part(p: Poly) -> bool:
    """Membership in Z + negative-outer-support Laurent-coefficient polynomials."""
    constant = F(0)
    for (g, n, k), a in p.items():
        if n != 0:
            raise ValueError("source must have u-degree zero")
        if g > 0:
            return False
        if g == 0:
            if k != 0:
                return False
            constant += a
    return constant.denominator == 1


def target_integer_part(p: Poly) -> bool:
    """Lexicographic exponent version of Z + strictly negative support."""
    constant = F(0)
    for (g, n, k), a in p.items():
        if (g, n) > (F(0), 0):
            return False
        if (g, n) == (F(0), 0):
            if k != 0:
                return False
            constant += a
    return constant.denominator == 1


def p_index(x: F) -> F:
    return 1 / (1 - x) if x < 0 else x + 1


def compression(x: F, a: F) -> F:
    return x if x <= a else a + (x - a) / (1 + x - a)


def jump(x: F, a: F) -> F:
    return x if x <= a else x + 1


def relative_index(x: F, c: F, v: F) -> F:
    return x if x >= v else v - (v - c) * (v - x) / (1 + v - x)


def run() -> dict[str, object]:
    COUNTS.clear()
    rng = random.Random(20260923)
    one: Poly = {(F(0), 0, 0): F(1)}

    # Individual Laurent powers, including all negative exponents in this range.
    for cutoff in (0, 1, 2, 4, 6, 8):
        for k in range(-8, 9):
            bk: Poly = {(F(0), 0, k): F(1)}
            inv: Poly = {(F(0), 0, -k): F(1)}
            check(mul(taylor(bk, cutoff), taylor(inv, cutoff), cutoff) == one,
                  "laurent_inverse", f"k={k}, N={cutoff}")
            check(taylor(taylor(bk, cutoff), cutoff, F(-1)) == bk,
                  "taylor_inverse_on_powers", f"k={k}, N={cutoff}")

    for cutoff in (1, 3, 5):
        for trial in range(100):
            x = random_poly(rng, cutoff)
            y = random_poly(rng, cutoff)
            tx, ty = taylor(x, cutoff), taylor(y, cutoff)
            check(taylor(add(x, y), cutoff) == add(tx, ty),
                  "additivity", f"trial={trial}, N={cutoff}")
            check(taylor(mul(x, y, cutoff), cutoff) == mul(tx, ty, cutoff),
                  "multiplicativity", f"trial={trial}, N={cutoff}")
            check(taylor(tx, cutoff, F(-1)) == x,
                  "taylor_inverse_general", f"trial={trial}, N={cutoff}")
            s, t = F(2, 3), F(-5, 4)
            check(taylor(taylor(x, cutoff, s), cutoff, t)
                  == taylor(x, cutoff, s + t),
                  "rational_parameter_composition", f"trial={trial}, N={cutoff}")

            src = random_poly(rng, cutoff, source=True)
            check(source_integer_part(src)
                  == target_integer_part(taylor(src, cutoff)),
                  "integer_part_reflection", f"trial={trial}, N={cutoff}")

    # Negative blocks remain negative no matter how many positive inner shifts.
    for q in (F(1, 7), F(1), F(17, 3)):
        for k in range(-6, 7):
            src = {( -q, 0, k): F(3, 2)}
            image = taylor(src, 12)
            check(all((g, n) < (F(0), 0) for g, n, _ in image),
                  "negative_block_sign", f"q={q}, k={k}")
            for integer in (-7, 0, 4):
                with_constant = add(src, {(F(0), 0, 0): F(integer)})
                check(target_integer_part(taylor(with_constant, 12)),
                      "integer_part_preservation", f"q={q}, k={k}, c={integer}")

    # No-gap counterexample: (b/2)t^-1 -> (b/2)t^-1 + 1/2.
    no_gap = {F(-1): {(1,): F(1, 2)}, F(0): {(0,): F(1, 2)}}
    check(no_gap[F(0)][(0,)].denominator != 1,
          "no_gap_counterexample", "fractional constant 1/2 is not an integer")
    gap_image = taylor({(F(-1), 0, 1): F(1, 2)}, 3)
    check(gap_image == {(F(-1), 0, 1): F(1, 2),
                        (F(-1), 1, 0): F(1, 2)},
          "gap_counterpart", "both image terms have negative outer exponent")

    grid = sorted({F(n, d) for d in (1, 2, 3, 7) for n in range(-30, 31)})
    a, c, v = F(2, 3), F(-7, 4), F(3, 5)
    maps: dict[str, Callable[[F], F]] = {
        "p": p_index,
        "negative_p": lambda x: -p_index(-x),
        "bounded_p": lambda x: p_index(x) / (1 + p_index(x)),
        "compression": lambda x: compression(x, a),
        "jump": lambda x: jump(x, a),
        "relative": lambda x: relative_index(x, c, v),
    }
    for name, function in maps.items():
        values = [function(x) for x in grid]
        for x, y in zip(values, values[1:]):
            check(x < y, "index_monotonicity", name)
    for x in grid:
        check(p_index(x) > 0, "index_range", "p > 0")
        check(F(0) < p_index(x)/(1+p_index(x)) < 1,
              "index_range", "bounded_p in (0,1)")
        check(compression(x, a) < a+1, "index_range", "compression below a+1")
        check(relative_index(x, c, v) > c, "index_range", "relative above c")
        if x <= a:
            check(compression(x, a) == x and jump(x, a) == x,
                  "parameter_fixation", "lower fixed segment")
        if x >= v:
            check(relative_index(x, c, v) == x,
                  "parameter_fixation", "upper fixed segment")

    # Rational separators underlying the continuum-family orientation proof.
    for a in (F(-2), F(0), F(3, 7), F(2)):
        for aprime in (F(-1), F(1, 5), F(1), F(4)):
            if a < aprime:
                q = (a + aprime) / 2
                check(a - q < 0 < aprime - q,
                      "orientation_separation", f"a={a}, a'={aprime}")

    return {
        "status": "passed",
        "arithmetic": "exact fractions; deterministic seed 20260923",
        "counts": dict(sorted(COUNTS.items())),
        "total_assertions": sum(COUNTS.values()),
        "scope": "finite and truncated Laurent/Taylor identities and rational index samples",
        "not_verified": [
            "arbitrary Hahn-support summability or well-ordering",
            "real-field derivations or their choice-dependent construction",
            "proper-class embeddings, classification, or image conjugacy theorems",
            "model-theoretic elementarity or nonelementarity",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="optional JSON report path")
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
