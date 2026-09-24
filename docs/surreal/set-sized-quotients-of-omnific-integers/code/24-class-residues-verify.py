#!/usr/bin/env python3
"""Deterministic finite checks for Beyond the Constant Term.

Python 3.9+; standard library only. These are finite sanity checks, not a
formal proof of any assertion about proper classes or infinite Hahn sums.
The default output is ../data/verification.json relative to this script.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
import platform
import random
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple


class Checks:
    def __init__(self) -> None:
        self.counts: Dict[str, int] = {}

    def check(self, group: str, condition: bool, detail: str) -> None:
        if not condition:
            raise AssertionError(f"{group}: {detail}")
        self.counts[group] = self.counts.get(group, 0) + 1


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def check_cyclic_rings(c: Checks, rng: random.Random) -> None:
    group = "greedy_ideals_in_Z_mod_n"
    for n in range(2, 45):
        divisors = [d for d in range(2, n + 1) if n % d == 0]
        for initial in divisors:
            orders: List[Sequence[int]] = [list(range(n)), list(reversed(range(n)))]
            for _ in range(8):
                order = list(range(n))
                rng.shuffle(order)
                orders.append(order)
            if n <= 5:
                orders.extend(itertools.permutations(range(n)))
            for order in orders:
                g = initial
                for x in order:
                    enlarged = math.gcd(g, x)
                    if enlarged != 1:
                        g = enlarged
                    c.check(group, g > 1 and initial % g == 0,
                            f"properness/extension n={n}, d={initial}")
                c.check(group, prime(g), f"maximality n={n}, divisor={g}")
                for x in range(n):
                    if x % g:
                        c.check(group, any((1 - r*x) % g == 0 for r in range(n)),
                                f"rejection inverse n={n}, g={g}, x={x}")


def check_boolean_products(c: Checks, rng: random.Random) -> None:
    group = "greedy_ideals_in_F2_products"
    for k in range(1, 9):
        full = (1 << k) - 1
        for _ in range(50):
            support = rng.randrange(full)  # A proper coordinate ideal.
            initial = support
            order = list(range(full + 1))
            rng.shuffle(order)
            for vector in order:
                proposed = support | vector
                if proposed != full:
                    support = proposed
                c.check(group, support != full and support | initial == support,
                        f"proper product ideal k={k}")
            missing = full ^ support
            c.check(group, missing != 0 and missing & (missing - 1) == 0,
                    f"exactly one surviving coordinate k={k}")


def check_geometric(c: Checks) -> None:
    group = "finite_geometric_remainders"
    for n in range(1, 161):
        # q_N/U = sum (-1)^j T^(-j-1). Exponent zero represents U.
        q = {-j - 1: (-1) ** j for j in range(n)}
        product: Dict[int, int] = {}
        for exponent, coefficient in q.items():
            product[exponent] = product.get(exponent, 0) + coefficient
            product[exponent + 1] = product.get(exponent + 1, 0) + coefficient
        product = {e: a for e, a in product.items() if a}
        expected = {0: 1, -n: (-1) ** (n - 1)}
        c.check(group, product == expected, f"N={n}")
        c.check(group, product[-n] != 0, f"finite tail cannot be discarded N={n}")
    # v=T-T^3 satisfies v^2=2 in Q[T]/(T^4+1).
    v = [0, 1, 0, -1]
    out = [0] * 4
    for i, ai in enumerate(v):
        for j, aj in enumerate(v):
            e = i + j
            out[e % 4] += ai * aj * (-1 if e >= 4 else 1)
    c.check(group, out == [2, 0, 0, 0], "quartic idempotent identity")


def eval_poly(coeff: Sequence[int], x: int, p: int) -> int:
    acc = 0
    for a in reversed(coeff):
        acc = (acc*x + a) % p
    return acc


def mul_mod_binomial(a: Sequence[int], b: Sequence[int], p: int) -> List[int]:
    """Multiply modulo T^m+1, where len(a)=len(b)=m."""
    m = len(a)
    if len(b) != m:
        raise ValueError("Different polynomial moduli")
    out = [0] * m
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                e = i + j
                out[e % m] = (out[e % m] + ai*bj*(-1 if e >= m else 1)) % p
    return out


def check_dyadic(c: Checks) -> None:
    group = "dyadic_CRT_and_idempotents_over_F257"
    p = 257
    old_roots: List[int] = []
    for n in range(8):
        m = 1 << n
        roots = [r for r in range(1, p) if pow(r, m, p) == p - 1]
        c.check(group, len(roots) == m, f"all roots distinct m={m}")
        total = [0] * m
        for r in roots:
            inv_r, inv_m = pow(r, -1, p), pow(m, -1, p)
            e = [(inv_m * pow(inv_r, j, p)) % p for j in range(m)]
            for s in roots:
                c.check(group, eval_poly(e, s, p) == int(s == r),
                        f"Lagrange factor m={m}, r={r}, s={s}")
            c.check(group, mul_mod_binomial(e, e, p) == e,
                    f"idempotence m={m}, r={r}")
            total = [(a+b) % p for a, b in zip(total, e)]
        c.check(group, total == [1] + [0]*(m-1), f"partition of unity m={m}")
        if old_roots:
            for r in old_roots:
                children = [s for s in roots if s*s % p == r]
                c.check(group, len(children) == 2, f"binary refinement m={m}, r={r}")
        old_roots = roots

    # Integer masks model idempotents in all finite binary product algebras.
    group = "finite_binary_branch_filters"
    for depth in range(1, 10):
        leaves = 1 << depth
        full = (1 << leaves) - 1
        for leaf in range(leaves):
            deepest = 1 << leaf
            forbidden = 0
            for length in range(depth + 1):
                prefix = leaf >> (depth - length)
                blocksize = 1 << (depth - length)
                selected = ((1 << blocksize) - 1) << (prefix * blocksize)
                c.check(group, selected & deepest == deepest,
                        "nested prefix idempotents")
                forbidden |= full ^ selected
            c.check(group, forbidden == full ^ deepest,
                    "branch equations produce coordinate maximal ideal")
            c.check(group, forbidden != full, "finite branch properness")


def lex_add(x: Tuple[Fraction, Fraction], y: Tuple[Fraction, Fraction]
            ) -> Tuple[Fraction, Fraction]:
    return (x[0] + y[0], x[1] + y[1])


def check_lexicographic(c: Checks) -> None:
    group = "lexicographic_scale_examples"
    zero = (Fraction(0), Fraction(0))
    a = (Fraction(0), Fraction(1))
    for high in range(1, 8):
        for low in range(-12, 13):
            b = (Fraction(high), Fraction(low))
            for n in range(1, 41):
                exponent = (b[0], b[1] - n)
                c.check(group, exponent > zero,
                        "dominant rank stays positive under finite subtraction")
                c.check(group, lex_add(exponent, (Fraction(0), Fraction(n))) == b,
                        "telescoping exponent reconstruction")
    for denominator in range(1, 12):
        for numerator in range(0, 45):
            b = (Fraction(0), Fraction(numerator, denominator))
            n = max(1, math.ceil(b[1]))
            complement = (Fraction(0), Fraction(n) - b[1])
            c.check(group, complement >= zero, "bounded-scale inverse exponent")
            c.check(group, lex_add(b, complement) == (Fraction(0), Fraction(n)),
                    "bounded-scale inverse monomial product")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "verification.json")
    args = parser.parse_args()
    c = Checks()
    rng = random.Random(20260923)
    check_cyclic_rings(c, rng)
    check_boolean_products(c, rng)
    check_geometric(c)
    check_dyadic(c)
    check_lexicographic(c)
    report = {
        "status": "all finite checks passed",
        "seed": 20260923,
        "python": platform.python_version(),
        "dependencies": "Python standard library only; Python 3.9+",
        "assertions_by_group": c.counts,
        "total_assertions": sum(c.counts.values()),
        "scope": "Finite examples and identities only. Not a formal proof of class recursion, "
                 "global choice, infinite Hahn sums, all surreal supports, or novelty."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
