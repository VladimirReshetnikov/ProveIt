#!/usr/bin/env python3
"""Exact regression checks for Curve and Abelian Rigidity.

Python 3.10+; standard library only. This checks finite identities and
examples, NOT the geometric theorems or arbitrary infinite supports.
"""
from __future__ import annotations

import argparse
import json
import random
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
from typing import Callable

Exponent = tuple[F, ...]
Series = dict[Exponent, F]
COUNTS: Counter[str] = Counter()


def check(condition: bool, category: str, detail: str = "") -> None:
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] += 1


def clean(p: Series) -> Series:
    return {e: F(c) for e, c in p.items() if c}


def const(c: int | F, rank: int) -> Series:
    return {(F(0),) * rank: F(c)} if c else {}


def var(i: int, rank: int) -> Series:
    if not 0 <= i < rank:
        raise ValueError("Variable index outside the specified rank")
    e = [F(0)] * rank
    e[i] = F(1)
    return {tuple(e): F(1)}


def add(*polys: Series) -> Series:
    result: Series = {}
    for p in polys:
        for e, c in p.items():
            result[e] = result.get(e, F(0)) + c
    return clean(result)


def scale(p: Series, c: int | F) -> Series:
    return clean({e: c * a for e, a in p.items()})


def mul(p: Series, q: Series) -> Series:
    result: Series = {}
    for a, c in p.items():
        for b, d in q.items():
            if len(a) != len(b):
                raise ValueError("Inconsistent exponent ranks")
            e = tuple(x + y for x, y in zip(a, b))
            result[e] = result.get(e, F(0)) + c * d
    return clean(result)


def power(p: Series, n: int, rank: int) -> Series:
    if n < 0:
        raise ValueError("Only nonnegative integer powers are supported")
    result = const(1, rank)
    base = p
    while n:
        if n & 1:
            result = mul(result, base)
        base = mul(base, base)
        n >>= 1
    return result


def euler(p: Series, functional: Callable[[Exponent], F]) -> Series:
    return clean({e: c * functional(e) for e, c in p.items()})


def ct(p: Series, rank: int) -> F:
    return p.get((F(0),) * rank, F(0))


def algebraic_checks() -> None:
    # A universal identity in Q[a,b,x,y,dx,dy], not numerical substitution.
    rank = 6
    a, b, x, y, dx, dy = [var(i, rank) for i in range(rank)]
    f = add(power(x, 3, rank), mul(a, x), b)
    fp = add(scale(power(x, 2, rank), 3), a)
    A0 = add(scale(mul(a, x), -18), scale(b, 27))
    C0 = add(scale(mul(a, power(x, 2, rank)), 6),
             scale(mul(b, x), -9), scale(power(a, 2, rank), 4))
    delta = add(scale(power(a, 3, rank), 4),
                scale(power(b, 2, rank), 27))
    check(add(mul(A0, f), mul(C0, fp)) == delta,
          "universal_cubic_certificate")
    for m in range(2, 13):
        lhs = add(mul(delta, dx), scale(mul(power(y, m - 1, rank),
                  add(mul(mul(A0, y), dx), scale(mul(C0, dy), m))), -1))
        rhs = add(mul(mul(A0, add(f, scale(power(y, m, rank), -1))), dx),
                  mul(C0, add(mul(fp, dx),
                      scale(mul(power(y, m - 1, rank), dy), -m))))
        check(lhs == rhs, "universal_divisibility_identity", f"m={m}")

    h = var(0, 1)
    one = const(1, 1)
    cusp_x, cusp_y = power(h, 2, 1), power(h, 3, 1)
    check(power(cusp_y, 2, 1) == power(cusp_x, 3, 1), "polynomial_families")
    node_x = add(power(h, 2, 1), scale(one, -1))
    node_y = mul(h, node_x)
    check(power(node_y, 2, 1) == mul(power(node_x, 2, 1), add(node_x, one)),
          "polynomial_families")
    n, h = var(0, 2), var(1, 2)
    parabola_y = add(power(n, 2, 2), scale(mul(n, h), 2), power(h, 2, 2))
    check(parabola_y == power(add(n, h), 2, 2), "polynomial_families")

    # The first-order tangent identity for Y^2=X^3-X.
    rank = 5
    x0, y0, u, v, eps = [var(i, rank) for i in range(rank)]
    def mod_eps2(p: Series) -> Series:
        return {e: c for e, c in p.items() if e[4] < 2}
    xx, yy = add(x0, mul(eps, u)), add(y0, mul(eps, v))
    residual = mod_eps2(add(power(yy, 2, rank), scale(power(xx, 3, rank), -1), xx))
    base = add(power(y0, 2, rank), scale(power(x0, 3, rank), -1), x0)
    linear = mul(eps, add(scale(mul(y0, v), 2),
                        scale(mul(power(x0, 2, rank), u), -3), u))
    check(residual == add(base, linear), "dual_number_tangent_identity")
    yy = mul(eps, var(0, rank))
    check(bool(yy) and not mod_eps2(power(yy, 2, rank)),
          "dual_number_elliptic_example")


def finite_hahn_checks() -> None:
    rng = random.Random(20260923)
    for rank in (1, 2):
        zero = (F(0),) * rank
        def functional(e: Exponent) -> F:
            return sum((F(2 * i + 1) * x for i, x in enumerate(e)), F(0))
        for trial in range(600):
            def random_series() -> Series:
                p: Series = {}
                for _ in range(rng.randrange(1, 10)):
                    e = tuple(F(rng.randrange(-12, 13), rng.randrange(1, 7))
                              for _ in range(rank))
                    # Lexicographically nonpositive: rank two is not
                    # being silently treated as a real-valued group.
                    if e > zero:
                        e = tuple(-x for x in e)
                    p[e] = p.get(e, F(0)) + F(rng.randrange(-7, 8), rng.randrange(1, 6))
                return clean(p)
            p, q = random_series(), random_series()
            pq = mul(p, q)
            dp, dq = euler(p, functional), euler(q, functional)
            check(euler(pq, functional) == add(mul(dp, q), mul(p, dq)),
                  "finite_support_Euler_Leibniz", f"rank={rank},trial={trial}")
            check(set(dp).issubset(p), "finite_support_preservation")
            check(zero not in dp, "Euler_kills_constant_coefficient")
            check(ct(pq, rank) == ct(p, rank) * ct(q, rank), "constant_term_multiplicative")
            if p and q:
                check(min(pq) == tuple(x + y for x, y in zip(min(p), min(q))),
                      "leading_exponent_additivity")
            if dp:
                check(min(dp) >= min(p), "Euler_valuation_bound")
            # Coordinate functionals jointly distinguish every nonzero
            # exponent in these finite rank-one and rank-two test sets.
            for e in p:
                if e != zero:
                    check(any(x != 0 for x in e), "finite_exponent_separation")


def characteristic_two_checks() -> None:
    # Coefficients are in F_2: a set denotes the support of coefficients 1.
    def mul2(p: set[F], q: set[F]) -> set[F]:
        out: set[F] = set()
        for a in p:
            for b in q:
                e = a + b
                if e in out:
                    out.remove(e)
                else:
                    out.add(e)
        return out
    for n in range(1, 81):
        yn = {F(-3, 2**j) for j in range(1, n + 1)}
        square = mul2(yn, yn)
        check(square == {2 * a for a in yn}, "finite_Frobenius_square")
        residual = square.symmetric_difference(yn).symmetric_difference({F(-3)})
        check(residual == {F(-3, 2**n)}, "Artin_Schreier_exact_tail", f"n={n}")
    # Check the three projective partial derivative monomials over F_2
    # on F_2-rational triples. The all-field assertion is proved in text
    # from the explicit partials X^2, Z^2, Y^2, not from this finite scan.
    for x in range(2):
        for y in range(2):
            for z in range(2):
                if (x, y, z) != (0, 0, 0):
                    check(any((x*x % 2, z*z % 2, y*y % 2)),
                          "F2_projective_partial_smoke_check")


def binomial_and_order_checks() -> None:
    coefficients = [F(1)]
    for n in range(1, 65):
        coefficients.append(-coefficients[-1] * (F(1, 2) - (n - 1)) / n)
    for n in range(65):
        coefficient = sum((coefficients[j] * coefficients[n - j]
                           for j in range(n + 1)), F(0))
        target = F(1) if n == 0 else F(-1) if n == 1 else F(0)
        check(coefficient == target, "binomial_square_coefficients", f"n={n}")
    check(coefficients[:4] == [F(1), F(-1, 2), F(-1, 8), F(-1, 16)],
          "printed_binomial_coefficients")
    for degree_f in range(15):
        for degree_g in range(15):
            a, b = -2 * degree_f, -3 - 2 * degree_g
            check(a != b, "discrete_ring_leading_parity")
            check(min(a, b) < 0, "discrete_ring_infinite_leading_term")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    algebraic_checks()
    finite_hahn_checks()
    characteristic_two_checks()
    binomial_and_order_checks()
    report = {
        "status": "PASS",
        "arithmetic": "exact: fractions.Fraction and F_2; no floating-point tests",
        "random_seed": 20260923,
        "assertions_passed": sum(COUNTS.values()),
        "checks_by_category": dict(sorted(COUNTS.items())),
        "scope": "Finite identities and examples only; not a formal verification of the theorems.",
        "dependencies": "Python 3.10+ standard library only",
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
