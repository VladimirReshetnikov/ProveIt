#!/usr/bin/env python3
"""Exact finite regression checks for article.tex.

Python 3.10+, standard library only. These tests check rational identities,
finite jets, and finite group words. They do not establish Hahn summability,
first-order definability, proper-class constructions, or theorem novelty.
Run: python3 verify.py
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json
import random

Exp = tuple[F, F, F]
Poly = dict[Exp, F]
Laurent = dict[int, int]
GroupElt = tuple[Laurent, int]
Jet = dict[tuple[int, int], F]
ZERO: Exp = (F(0), F(0), F(0))
ONE: Poly = {ZERO: F(1)}
COUNTS: Counter[str] = Counter()
RNG = random.Random(20260923)


def check(condition: bool, category: str, detail: str = "") -> None:
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] += 1


def plus(a: Exp, b: Exp) -> Exp:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def times(n: F, a: Exp) -> Exp:
    return tuple(n * x for x in a)  # type: ignore[return-value]


def dot(a: Exp, b: Exp) -> F:
    return sum((x * y for x, y in zip(a, b)), F(0))


def clean(p: Poly) -> Poly:
    return {g: c for g, c in p.items() if c}


def add(p: Poly, q: Poly) -> Poly:
    out = dict(p)
    for g, c in q.items():
        out[g] = out.get(g, F(0)) + c
    return clean(out)


def scale(c: F, p: Poly) -> Poly:
    return clean({g: c * a for g, a in p.items()})


def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for g, a in p.items():
        for h, b in q.items():
            e = plus(g, h)
            out[e] = out.get(e, F(0)) + a * b
    return clean(out)


def deriv(p: Poly, phi: Exp, delta: Exp) -> Poly:
    return clean({plus(g, times(F(-1), delta)): a * dot(phi, g)
                  for g, a in p.items()})


def falling(a: F, c: F, n: int) -> F:
    result = F(1)
    for j in range(n):
        result *= a - j * c
    return result


def exp_coeff(a: F, c: F, s: F, n: int) -> F:
    return s**n * falling(a, c, n) / factorial(n)


def rand_exp() -> Exp:
    return tuple(F(RNG.randint(-4, 4), RNG.randint(1, 3))
                 for _ in range(3))  # type: ignore[return-value]


def rand_poly() -> Poly:
    return clean({rand_exp(): F(RNG.randint(-4, 4)) for _ in range(5)})


def determinant(matrix: list[list[F]]) -> F:
    a = [row[:] for row in matrix]
    n = len(a)
    result = F(1)
    for col in range(n):
        pivot = next((j for j in range(col, n) if a[j][col]), None)
        if pivot is None:
            return F(0)
        if pivot != col:
            a[pivot], a[col] = a[col], a[pivot]
            result = -result
        p = a[col][col]
        result *= p
        for j in range(col + 1, n):
            ratio = a[j][col] / p
            for k in range(col + 1, n):
                a[j][k] -= ratio * a[col][k]
    return result


def la(p: Laurent, q: Laurent) -> Laurent:
    out = dict(p)
    for n, k in q.items():
        out[n] = out.get(n, 0) + k
    return {n: k for n, k in out.items() if k}


def shift(p: Laurent, n: int) -> Laurent:
    return {j + n: k for j, k in p.items()}


def gm(a: GroupElt, b: GroupElt) -> GroupElt:
    p, m = a
    q, n = b
    return la(p, shift(q, m)), m + n


def gi(a: GroupElt) -> GroupElt:
    p, m = a
    return {j - m: -k for j, k in p.items()}, -m


def comm(a: GroupElt, b: GroupElt) -> GroupElt:
    return gm(gm(gm(a, b), gi(a)), gi(b))


def rand_group() -> GroupElt:
    p = {n: RNG.randint(-3, 3) for n in RNG.sample(range(-4, 5), 4)}
    return {n: k for n, k in p.items() if k}, RNG.randint(-4, 4)


def jm(a: Jet, b: Jet, umax: int, vmax: int) -> Jet:
    out: Jet = {}
    for (i, j), x in a.items():
        for (k, ell), y in b.items():
            if i + k <= umax and j + ell <= vmax:
                e = (i + k, j + ell)
                out[e] = out.get(e, F(0)) + x * y
    return {e: x for e, x in out.items() if x}


def jp(a: Jet, n: int, umax: int, vmax: int) -> Jet:
    out: Jet = {(0, 0): F(1)}
    for _ in range(n):
        out = jm(out, a, umax, vmax)
    return out


def ja(a: Jet, b: Jet) -> Jet:
    out = dict(a)
    for e, x in b.items():
        out[e] = out.get(e, F(0)) + x
    return {e: x for e, x in out.items() if x}


def main() -> None:
    delta: Exp = (F(0), F(0), F(1))
    epsilon: Exp = (F(0), F(1), F(0))

    for trial in range(60):
        p, q = rand_poly(), rand_poly()
        phi, psi = rand_exp(), rand_exp()
        lhs = deriv(mul(p, q), phi, delta)
        rhs = add(mul(deriv(p, phi, delta), q), mul(p, deriv(q, phi, delta)))
        check(lhs == rhs, "finite_Leibniz", str(trial))
        lhs = add(deriv(deriv(p, psi, epsilon), phi, delta),
                  scale(F(-1), deriv(deriv(p, phi, delta), psi, epsilon)))
        beta = plus(times(dot(psi, delta), phi),
                    times(-dot(phi, epsilon), psi))
        check(lhs == deriv(p, beta, plus(delta, epsilon)),
              "derivation_bracket", str(trial))
        g = rand_exp()
        actual = {g: F(1)}
        for n in range(9):
            expected = clean({plus(g, times(F(-n), delta)):
                              falling(dot(phi, g), dot(phi, delta), n)})
            check(actual == expected, "falling_factorial_iterates", f"{trial}, {n}")
            actual = deriv(actual, phi, delta)

    for trial in range(40):
        a, b, c, s, t = (F(RNG.randint(-5, 5), RNG.randint(1, 3)) for _ in range(5))
        for r in range(11):
            composition = sum((exp_coeff(a, c, t, n) *
                               exp_coeff(a - n*c, c, s, r-n)
                               for n in range(r + 1)), F(0))
            check(composition == exp_coeff(a, c, s+t, r),
                  "flow_composition_jets", f"{trial}, {r}")
            product = sum((exp_coeff(a, c, s, j) * exp_coeff(b, c, s, r-j)
                           for j in range(r + 1)), F(0))
            check(product == exp_coeff(a+b, c, s, r),
                  "flow_product_jets", f"{trial}, {r}")

    # Finite sign tests are sanity checks, not the universal threshold proof.
    for trial in range(200):
        g = rand_exp()
        if g < ZERO:
            g = times(F(-1), g)
        if g > ZERO and g[1] != 0:
            for n in range(21):
                check(plus(g, times(F(-n), delta)) > ZERO,
                      "convex_threshold_finite_samples", f"{g}, {n}")
        if g > ZERO and g[0] != 0:
            for n in range(21):
                check(plus(g, times(F(-n), epsilon)) > ZERO,
                      "second_scale_finite_samples", f"{g}, {n}")

    for r in range(1, 9):
        for trial in range(10):
            nodes = RNG.sample(range(-15, 16), r)
            matrix = [[F((-n)**j, factorial(j)) for n in nodes] for j in range(r)]
            expected = F(1)
            for i in range(r):
                expected /= factorial(i)
                for j in range(i + 1, r):
                    expected *= nodes[i] - nodes[j]
            check(determinant(matrix) == expected and expected != 0,
                  "Vandermonde_determinants", str(nodes))

    identity: GroupElt = ({}, 0)
    generator_a: GroupElt = ({}, 1)
    generator_b: GroupElt = ({0: 1}, 0)
    for trial in range(100):
        a, b, c = rand_group(), rand_group(), rand_group()
        check(gm(gm(a, b), c) == gm(a, gm(b, c)), "semidirect_associativity")
        check(gm(a, gi(a)) == identity and gm(gi(a), a) == identity,
              "semidirect_inverses")
    for n in range(-12, 13):
        check(gm(gm(({}, n), generator_b), ({}, -n)) == ({n: 1}, 0),
              "conjugation_shift")
    current = generator_b
    for r in range(13):
        expected = {j: (-1)**(r-j) * comb(r, j) for j in range(r + 1)}
        check(current == (expected, 0), "iterated_commutator_group_words", str(r))
        current = comm(generator_a, current)

    # Exact two-variable jets: u is the smaller infinitesimal, so valuation
    # is lexicographic in (u-power, v-power), reflecting u=omega^-omega.
    umax, vmax = 3, 12
    exp_minus_one: Jet = {(0, j): F((-1)**j, factorial(j)) for j in range(1, vmax+1)}
    for r in range(9):
        power = jp(exp_minus_one, r, umax, vmax)
        h = {(1, j): x for (i, j), x in power.items() if i == 0}
        check(min(h) == (1, r) and h[(1, r)] == (-1)**r,
              "commutator_phase_leading_jets", str(r))
        displacement: Jet = {}
        for n in range(1, umax + 1):
            term = jp(h, n, umax, vmax)
            displacement = ja(displacement, {e: x/factorial(n) for e, x in term.items()})
        check(min(displacement) == (1, r) and displacement[(1, r)] == (-1)**r,
              "commutator_exponential_leading_jets", str(r))

    u, v = 1, 0
    for n in range(33):
        check(u*u - 2*v*v == 1 and u >= 3**n, "Pell_recurrence", str(n))
        u, v = 3*u + 4*v, 2*u + 3*v

    report = {
        "status": "PASS",
        "arithmetic": "Exact fractions and integers; no floating-point tests",
        "random_seed": 20260923,
        "checks_by_category": dict(sorted(COUNTS.items())),
        "total_checks": sum(COUNTS.values()),
        "scope": "Finite algebraic regression tests only; not formal verification of the theorems.",
        "not_tested": ["Hahn support well-ordering", "Proper-class constructions",
                       "First-order definability", "Historical novelty"]
    }
    output = Path(__file__).with_name("verification.json")
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
