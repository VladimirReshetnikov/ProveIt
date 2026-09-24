#!/usr/bin/env python3
"""Exact finite regression tests for the accompanying research manuscript.

These tests do NOT certify the infinite Hahn, geometric, or Galois theorems.
Run from any directory: python3 code/verify.py [--output PATH]
Requires Python >= 3.10 and SymPy. No network access or floating arithmetic.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import factorial
from pathlib import Path
import json
import random
import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install SymPy before running: python -m pip install sympy") from exc

COUNTS: Counter[str] = Counter()


def check(group: str, condition: bool, detail: str = "") -> None:
    if not condition:
        raise AssertionError(f"{group}: {detail}")
    COUNTS[group] += 1


def mul(a: list[Q], b: list[Q], order: int) -> list[Q]:
    out = [Q(0) for _ in range(order + 1)]
    for i, x in enumerate(a[:order + 1]):
        if not x:
            continue
        for j, y in enumerate(b[:order + 1 - i]):
            out[i + j] += x * y
    return out


def power(a: list[Q], n: int, order: int) -> list[Q]:
    if n < 0:
        raise ValueError("Only nonnegative integer powers are supported")
    out = [Q(1)] + [Q(0)] * order
    base = a[:order + 1]
    while n:
        if n & 1:
            out = mul(out, base, order)
        base = mul(base, base, order)
        n >>= 1
    return out


def radical(a: Q, n: int, order: int) -> list[Q]:
    if n < 1:
        raise ValueError("Root degree must be positive")
    out = [Q(1)]
    for j in range(1, order + 1):
        out.append(out[-1] * (Q(1, n) - j + 1) * (-a) / j)
    return out


def sparse_mul(a: dict[Q, Q], b: dict[Q, Q]) -> dict[Q, Q]:
    out: dict[Q, Q] = {}
    for x, c in a.items():
        for y, d in b.items():
            out[x + y] = out.get(x + y, Q(0)) + c * d
    return {x: c for x, c in out.items() if c}


def residue(q: Q) -> Q:
    return q - q.numerator // q.denominator


def binomial_checks() -> None:
    order = 16
    avals = [Q(-3), Q(-1), Q(-1, 2), Q(1, 3), Q(1), Q(2), Q(5)]
    for a, n in product(avals, range(2, 11)):
        r = radical(a, n, order)
        got = power(r, n, order)
        expected = [Q(1), -a] + [Q(0)] * (order - 1)
        for j, (x, y) in enumerate(zip(got, expected)):
            check("normalized_radical_powers", x == y, f"a={a},n={n},j={j}")
    for a, m, n in product(avals, range(2, 6), range(2, 7)):
        lhs = power(radical(a, m * n, order), m, order)
        rhs = radical(a, n, order)
        for j, (x, y) in enumerate(zip(lhs, rhs)):
            check("compatible_radical_towers", x == y, f"a={a},m={m},n={n},j={j}")
    r = radical(Q(1), 2, 4)
    check("displayed_coefficients", r == [Q(1), Q(-1, 2), Q(-1, 8),
                                          Q(-1, 16), Q(-5, 128)])


def coset_checks(rng: random.Random) -> None:
    for d in range(2, 14):
        for trial in range(12):
            a = {Q(j, d): Q(rng.randint(-4, 4)) for j in range(-18, 24)}
            a = {x: c for x, c in a.items() if c}
            x = {Q(j): Q(rng.randint(-3, 3)) for j in range(-3, 11)}
            x = {e: c for e, c in x.items() if c}
            ax = sparse_mul(a, x)
            for r in (Q(j, d) for j in range(d)):
                project_a = {e: c for e, c in a.items() if residue(e) == r}
                project_ax = {e: c for e, c in ax.items() if residue(e) == r}
                check("cyclic_coset_projection", project_ax == sparse_mul(project_a, x),
                      f"d={d}, trial={trial}, residue={r}")
                exponents = [(e - r) for e in project_a]
                check("integer_coset_coordinates", all(e.denominator == 1 for e in exponents))


def polynomial_checks() -> dict[str, str]:
    X, z = sp.symbols("X z")
    discs: dict[str, str] = {}
    for m in range(2, 10):
        p = X**m - X - z
        disc = sp.Poly(sp.discriminant(p, X), z)
        discs[str(m)] = str(disc.as_expr())
        check("symmetric_polynomial_discriminants", disc.degree() == m - 1)
        check("symmetric_polynomial_discriminants", sp.gcd(disc, disc.diff()).degree() == 0)
        check("symmetric_polynomial_discriminants", disc.eval(0) != 0)
        critical = sp.Poly(m * X**(m - 1) - 1, X)
        check("simple_critical_points", sp.gcd(critical, critical.diff()).degree() == 0)
        # The critical value identity modulo the derivative.
        rem = sp.rem(X**m - X + sp.Rational(m - 1, m) * X, critical.as_expr(), X)
        check("critical_value_formula", rem == 0)
        fiber = sp.Poly(X**m - X, X)
        check("split_simple_zero_fiber", sp.gcd(fiber, fiber.diff()).degree() == 0)

    order = 20
    for m in range(2, 9):
        x = [Q(0)] * (order + 1)
        for _ in range(order + 2):
            new = power(x, m, order)
            new[1] -= 1
            x = new
        p = power(x, m, order)
        p = [c - d for c, d in zip(p, x)]
        p[1] -= 1
        for j, c in enumerate(p):
            check("implicit_local_series", c == 0, f"m={m},j={j}")
        if m == 5:
            check("displayed_coefficients", x[1] == -1 and x[5] == -1 and x[9] == -5)
    return discs


def crt_checks() -> None:
    X = sp.Symbol("X")
    for n in range(2, 9):
        roots = list(range(1, n + 1))
        p = sp.Poly(sp.prod(X - r for r in roots), X, domain=sp.QQ)
        idempotents = []
        for r in roots:
            e = sp.prod((X - s) / Q(r - s) for s in roots if s != r)
            idempotents.append(sp.Poly(e.expand(), X, domain=sp.QQ))
        check("chinese_remainder_splitting", sum(idempotents, sp.Poly(0, X, domain=sp.QQ)) == sp.Poly(1, X, domain=sp.QQ))
        for i, j in product(range(n), repeat=2):
            prod = (idempotents[i] * idempotents[j]).rem(p)
            want = idempotents[i] if i == j else sp.Poly(0, X, domain=sp.QQ)
            check("chinese_remainder_splitting", prod == want)
            check("chinese_remainder_evaluation", idempotents[i].eval(roots[j]) == int(i == j))


def permutation_checks() -> None:
    for n in range(2, 7):
        identity = tuple(range(n))
        seen = {identity}
        frontier = [identity]
        while frontier:
            p = frontier.pop()
            for j in range(n - 1):
                q = list(p)
                q[j], q[j + 1] = q[j + 1], q[j]
                new = tuple(q)
                if new not in seen:
                    seen.add(new)
                    frontier.append(new)
        check("transposition_generation", len(seen) == factorial(n))


def real_symmetry_checks(rng: random.Random) -> None:
    def multiply(a: tuple[int, int, int], b: tuple[int, int, int], n: int) -> tuple[int, int, int]:
        x, y, e = a
        xx, yy, f = b
        sign = 1 if e == 0 else -1
        return ((x + sign * xx) % n, (y + sign * yy) % n, (e + f) % 2)
    for n in range(2, 10):
        conjugation = (0, 0, 1)
        for x, y in product(range(n), repeat=2):
            a = (x, y, 0)
            lhs = multiply(multiply(conjugation, a, n), conjugation, n)
            check("conjugation_inversion", lhs == ((-x) % n, (-y) % n, 0))
        for _ in range(80):
            a, b, c = [(rng.randrange(n), rng.randrange(n), rng.randrange(2)) for _ in range(3)]
            lhs = multiply(multiply(a, b, n), c, n)
            rhs = multiply(a, multiply(b, c, n), n)
            check("finite_semidirect_associativity", lhs == rhs)


def lexicographic_checks(rng: random.Random) -> None:
    for dimension in range(1, 7):
        h = (Q(1),) + (Q(0),) * dimension
        zero = (Q(0),) * (dimension + 1)
        for _ in range(100):
            old = (Q(0),) + tuple(Q(rng.randint(-1000, 1000), rng.randint(1, 20))
                                    for _ in range(dimension))
            shifted = tuple(x - y for x, y in zip(old, h))
            check("dominating_scale_samples", old < h)
            check("negative_numerator_support_samples", shifted < zero)
            recovered = tuple(x + y for x, y in zip(shifted, h))
            check("uniform_denominator_shift", recovered == old)


def main() -> None:
    default = Path(__file__).resolve().parents[1] / "data" / "verification_results.json"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=default)
    args = parser.parse_args()
    rng = random.Random(20260923)
    binomial_checks()
    coset_checks(rng)
    discriminants = polynomial_checks()
    crt_checks()
    permutation_checks()
    real_symmetry_checks(rng)
    lexicographic_checks(rng)
    result = {
        "status": "all finite checks passed",
        "seed": 20260923,
        "python": sys.version.split()[0],
        "sympy": sp.__version__,
        "assertions": dict(sorted(COUNTS.items())),
        "total_assertions": sum(COUNTS.values()),
        "discriminants_X_m_minus_X_minus_z": discriminants,
        "scope": "Exact finite identities only. Not a formal proof of the manuscript's infinite statements."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
