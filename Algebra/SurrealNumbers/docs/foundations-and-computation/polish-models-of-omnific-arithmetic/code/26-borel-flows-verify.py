#!/usr/bin/env python3
"""Exact finite checks for 'Borel Flows on Left-Finite Series Fields'.

Python 3.10+; standard library only. No floating-point exponent arithmetic.
These checks do NOT certify Baire-category or infinite-support arguments.
Every check remains active under python -O.
"""
from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction as Q
from pathlib import Path
from typing import Callable

Monomial = tuple[tuple[int, int], ...]
Polynomial = dict[Monomial, Q]
Derivation = Callable[[Polynomial], Polynomial]
CHECKS = 0


def check(condition: bool, description: str) -> None:
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ArithmeticError(f"Check {CHECKS} failed: {description}")


def clean(p: Polynomial) -> Polynomial:
    return {m: Q(c) for m, c in p.items() if c}


def const(c: Q | int) -> Polynomial:
    return {(): Q(c)} if c else {}


def var(i: int) -> Polynomial:
    if i < 0:
        raise ValueError("Variable index must be nonnegative")
    return {((i, 1),): Q(1)}


def add(p: Polynomial, q: Polynomial) -> Polynomial:
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, Q(0)) + c
    return clean(r)


def scale(p: Polynomial, c: Q | int) -> Polynomial:
    return clean({m: Q(c) * a for m, a in p.items()})


def mul_monomials(m: Monomial, n: Monomial) -> Monomial:
    powers = dict(m)
    for i, k in n:
        powers[i] = powers.get(i, 0) + k
    return tuple(sorted((i, k) for i, k in powers.items() if k))


def mul(p: Polynomial, q: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for m, a in p.items():
        for n, b in q.items():
            mn = mul_monomials(m, n)
            out[mn] = out.get(mn, Q(0)) + a * b
    return clean(out)


def power(p: Polynomial, n: int) -> Polynomial:
    if n < 0:
        raise ValueError("Polynomial powers must be nonnegative")
    ans = const(1)
    base = p
    while n:
        if n & 1:
            ans = mul(ans, base)
        base = mul(base, base)
        n >>= 1
    return ans


def derivative(p: Polynomial, parity: int | None) -> Polynomial:
    """zi -> zi+1 on selected parity, zero on the other parity."""
    out: Polynomial = {}
    for m, c in p.items():
        for i, k in m:
            if parity is not None and i % 2 != parity:
                continue
            d = dict(m)
            d[i] -= 1
            d[i + 1] = d.get(i + 1, 0) + 1
            new_m = tuple(sorted((j, a) for j, a in d.items() if a))
            out[new_m] = out.get(new_m, Q(0)) + k * c
    return clean(out)


def E(p: Polynomial) -> Polynomial:
    return derivative(p, 0)


def F(p: Polynomial) -> Polynomial:
    return derivative(p, 1)


def D(p: Polynomial) -> Polynomial:
    return derivative(p, None)


def H(p: Polynomial) -> Polynomial:
    return add(E(F(p)), scale(F(E(p)), -1))


def bracket_direct(p: Polynomial) -> Polynomial:
    """Independent product-rule implementation: zi -> (-1)^(i+1) zi+2."""
    out: Polynomial = {}
    for m, c in p.items():
        for i, k in m:
            d = dict(m)
            d[i] -= 1
            d[i + 2] = d.get(i + 2, 0) + 1
            new_m = tuple(sorted((j, a) for j, a in d.items() if a))
            sign = -1 if i % 2 == 0 else 1
            out[new_m] = out.get(new_m, Q(0)) + sign * k * c
    return clean(out)


def shear(p: Polynomial, parity: int, s: Q) -> Polynomial:
    out: Polynomial = {}
    for m, c in p.items():
        term = const(c)
        for i, k in m:
            image = add(var(i), scale(var(i + 1), s)) if i % 2 == parity else var(i)
            term = mul(term, power(image, k))
        out = add(out, term)
    return out


def A(p: Polynomial) -> Polynomial:
    # A = P_1 after Q_1; order matters.
    return shear(shear(p, 1, Q(1)), 0, Q(1))


def random_polynomial(rng: random.Random) -> Polynomial:
    out: Polynomial = {}
    for _ in range(rng.randint(1, 5)):
        term = const(Q(rng.randint(-4, 4), rng.randint(1, 5)))
        for _ in range(rng.randint(0, 3)):
            term = mul(term, var(rng.randrange(7)))
        out = add(out, term)
    return out


def binom(q: Q, n: int) -> Q:
    r = Q(1)
    for j in range(n):
        r *= (q - j) / (j + 1)
    return r


def exp_coefficient(q: Q, s: Q, n: int) -> Q:
    # D=t^2 d/dt: D^n(t^q)/n! = (q)^(rising n) t^(q+n)/n!
    r = Q(1)
    for j in range(n):
        r *= (q + j) / (j + 1)
    return r * s**n


def run_checks() -> dict[str, object]:
    global CHECKS
    CHECKS = 0
    rng = random.Random(20261004)
    stages: dict[str, int] = {}
    before = CHECKS

    for i in range(24):
        check(E(var(i)) == (var(i + 1) if i % 2 == 0 else {}), "E basis")
        check(F(var(i)) == (var(i + 1) if i % 2 == 1 else {}), "F basis")
        check(H(var(i)) == scale(var(i + 2), -1 if i % 2 == 0 else 1), "bracket basis")
        x = var(i)
        y = var(i)
        for n in range(33):
            check(x == var(i + n), "D iterated chain")
            check(y == scale(var(i + 2 * n), (-1 if i % 2 == 0 else 1)**n),
                  "H iterated chain")
            x, y = D(x), H(y)
    stages["basis_and_iterated_chains"] = CHECKS - before
    before = CHECKS

    for _ in range(100):
        p, q = random_polynomial(rng), random_polynomial(rng)
        check(D(p) == add(E(p), F(p)), "D=E+F on polynomials")
        check(H(p) == bracket_direct(p), "independent bracket formula")
        for deriv in (E, F, D, H):
            check(deriv(mul(p, q)) == add(mul(deriv(p), q), mul(p, deriv(q))),
                  "Leibniz on polynomial pair")
        s = Q(rng.randint(-3, 3), rng.randint(1, 4))
        t = Q(rng.randint(-3, 3), rng.randint(1, 4))
        for parity in (0, 1):
            check(shear(shear(p, parity, t), parity, s) == shear(p, parity, s + t),
                  "shear group law")
            check(shear(shear(p, parity, -s), parity, s) == p, "shear inverse")
            check(shear(mul(p, q), parity, s)
                  == mul(shear(p, parity, s), shear(q, parity, s)),
                  "shear multiplicativity")
    stages["polynomial_derivation_and_shear_laws"] = CHECKS - before
    before = CHECKS

    x = var(0)
    pivots = [0]
    for k in range(1, 41):
        x = A(x)
        indices: list[int] = []
        for m in x:
            check(len(m) == 1 and m[0][1] == 1, "A orbit remains degree one")
            indices.append(m[0][0])
        largest = max(indices)
        check(largest == 2 * k - 1, "integer orbit new largest index")
        check(x.get(((largest, 1),)) == Q(1), "integer orbit pivot coefficient one")
        check(largest > pivots[-1], "strictly increasing finite independence pivots")
        pivots.append(largest)
    stages["time_one_independence_certificates"] = CHECKS - before
    before = CHECKS

    qs = [Q(-3), Q(-1, 2), Q(0), Q(1, 3), Q(1), Q(5, 2)]
    times = [(Q(1, 2), Q(-2, 3)), (Q(-1), Q(2)), (Q(0), Q(3, 4))]
    for q in qs:
        for s, t in times:
            for n in range(21):
                check(exp_coefficient(q, s, n) == binom(-q, n) * (-s)**n,
                      "rational binomial vs iterated uniform-gain exponential")
                composed = sum((exp_coefficient(q, t, k)
                                * exp_coefficient(q + k, s, n - k)
                                for k in range(n + 1)), Q(0))
                check(composed == exp_coefficient(q, s + t, n),
                      "uniform-gain flow composition coefficient")
    stages["rational_binomial_uniform_gain"] = CHECKS - before

    return {
        "status": "PASS",
        "arithmetic": "exact fractions; independent formal variable indices",
        "checks": CHECKS,
        "stage_checks": stages,
        "bounds": {
            "basis_indices": "0 through 23",
            "chain_iteration_orders": "0 through 32",
            "deterministic_polynomial_pairs": 100,
            "time_one_powers": "1 through 40",
            "uniform_gain_coefficient_orders": "0 through 20",
            "random_seed": 20261004,
        },
        "time_one_pivot_indices": pivots,
        "scope": "Finite algebraic identities only; not a proof of infinite-support or Baire assertions.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="Write a reproducible JSON receipt")
    args = parser.parse_args()
    receipt = run_checks()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.json is not None:
        args.json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
