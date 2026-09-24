#!/usr/bin/env python3
"""Exact finite checks for 'All Derivations Integrate'.

Standard library only.  Model: A0 = Z + X*Q[X], with finite T-jets.
These checks test operator identities, not surreal supports or class logic.
Run: python code/verify.py --output data/verification.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json
import random
from typing import Callable

Poly = dict[int, F]
Jet = list[Poly]
PMap = Callable[[Poly], Poly]
JMap = Callable[[Jet], Jet]
COUNTS: Counter[str] = Counter()


def check(group: str, actual: object, expected: object) -> None:
    if actual != expected:
        raise AssertionError(f"{group}: {actual!r} != {expected!r}")
    COUNTS[group] += 1


def clean(p: Poly) -> Poly:
    return {k: F(v) for k, v in p.items() if v}


def pa(p: Poly, q: Poly) -> Poly:
    z = dict(p)
    for k, v in q.items():
        z[k] = z.get(k, F(0)) + v
    return clean(z)


def ps(p: Poly, c: F | int) -> Poly:
    return clean({k: v * c for k, v in p.items()})


def pm(p: Poly, q: Poly) -> Poly:
    z: Poly = {}
    for k, a in p.items():
        for l, b in q.items():
            z[k + l] = z.get(k + l, F(0)) + a * b
    return clean(z)


def euler(m: int) -> PMap:
    """E_m = X^(m+1) d/dX: acts inside Z + X Q[X]."""
    if m < 0:
        raise ValueError("m must be nonnegative")
    return lambda p: clean({k + m: k * v for k, v in p.items() if k})


def pcomb(terms: list[tuple[F, int]]) -> PMap:
    def result(p: Poly) -> Poly:
        z: Poly = {}
        for c, m in terms:
            z = pa(z, ps(euler(m)(p), c))
        return z
    return result


def iterate(d: PMap, p: Poly, n: int) -> Poly:
    for _ in range(n):
        p = d(p)
    return p


def zero(n: int) -> Jet:
    return [{} for _ in range(n + 1)]


def constant(p: Poly, n: int) -> Jet:
    z = zero(n)
    z[0] = p
    return z


def ja(p: Jet, q: Jet) -> Jet:
    if len(p) != len(q):
        raise ValueError("jet orders differ")
    return [pa(a, b) for a, b in zip(p, q)]


def js(p: Jet, c: F | int) -> Jet:
    return [ps(a, c) for a in p]


def jm(p: Jet, q: Jet) -> Jet:
    n = len(p) - 1
    if len(q) != n + 1:
        raise ValueError("jet orders differ")
    z = zero(n)
    for k in range(n + 1):
        for j in range(k + 1):
            z[k] = pa(z[k], pm(p[j], q[k - j]))
    return z


def lie(terms: list[tuple[int, PMap]]) -> JMap:
    if any(j < 1 for j, _ in terms):
        raise ValueError("a Lie series must increase T-order")
    def result(p: Jet) -> Jet:
        n = len(p) - 1
        z = zero(n)
        for shift, d in terms:
            for k in range(n + 1 - shift):
                z[k + shift] = pa(z[k + shift], d(p[k]))
        return z
    return result


def exp_apply(l: JMap, p: Jet) -> Jet:
    z = p
    term = p
    for k in range(1, len(p)):
        term = l(term)
        z = ja(z, js(term, F(1, factorial(k))))
    return z


def log_apply(phi: JMap, p: Jet) -> Jet:
    z = zero(len(p) - 1)
    term = p
    for k in range(1, len(p)):
        term = ja(phi(term), js(term, -1))
        z = ja(z, js(term, F((-1) ** (k + 1), k)))
    return z


def in_a0(p: Poly) -> bool:
    return p.get(0, F(0)).denominator == 1


def random_poly(rng: random.Random, degree: int = 4) -> Poly:
    p: Poly = {0: F(rng.randint(-3, 3))}
    for k in range(1, degree + 1):
        p[k] = F(rng.randint(-4, 4), rng.randint(1, 5))
    return clean(p)


def hs_checks(rng: random.Random) -> None:
    for _ in range(36):
        p, q = random_poly(rng), random_poly(rng)
        d = pcomb([(F(rng.randint(-2, 2), 2), 0), (F(1), 1)])
        check("ordinary_leibniz", d(pm(p, q)), pa(pm(d(p), q), pm(p, d(q))))
        check("divisible_ideal_image", d(p).get(0, F(0)), F(0))
        hp = [ps(iterate(d, p, n), F(1, factorial(n))) for n in range(6)]
        hq = [ps(iterate(d, q, n), F(1, factorial(n))) for n in range(6)]
        hpq = [ps(iterate(d, pm(p, q), n), F(1, factorial(n))) for n in range(6)]
        product = jm(hp, hq)
        for n in range(6):
            check("hasse_schmidt_product", hpq[n], product[n])
            check("integral_coefficients", in_a0(hp[n]), True)
        for r in range(4):
            for s in range(4):
                lhs = ps(iterate(d, ps(iterate(d, p, s), F(1, factorial(s))), r),
                         F(1, factorial(r)))
                rhs = ps(iterate(d, p, r + s), F(comb(r + s, r), factorial(r + s)))
                check("iterativity", lhs, rhs)


def formal_checks(rng: random.Random) -> None:
    for n in range(1, 6):
        for _ in range(5):
            p = [random_poly(rng, 3) for _ in range(n + 1)]
            q = [random_poly(rng, 2) for _ in range(n + 1)]
            l = lie([(1, pcomb([(F(1), 0), (F(1, 2), 1)])),
                     (2, euler(1)), (3, euler(2))])
            negative = lambda z, l=l: js(l(z), -1)
            phi = lambda z, l=l: exp_apply(l, z)
            check("exp_log", log_apply(phi, p), l(p))
            check("exp_inverse", phi(exp_apply(negative, p)), p)
            check("formal_multiplicativity", phi(jm(p, q)), jm(phi(p), phi(q)))
            t = zero(n)
            t[1] = {0: F(1)}
            check("parameter_fixed", phi(t), t)
            check("identity_residue", phi(p)[0], p[0])
            for coefficient in phi(p):
                check("integral_formal_coefficients", in_a0(coefficient), True)
            # Exercise the opposite exp(log(.)) identity at low degree.
            if n <= 3:
                logarithm = lambda z, phi=phi: log_apply(phi, z)
                check("log_exp", exp_apply(logarithm, p), phi(p))


def commutator_checks(rng: random.Random) -> None:
    for m in range(5):
        for n in range(5):
            for _ in range(4):
                p = random_poly(rng)
                lhs = pa(euler(m)(euler(n)(p)), ps(euler(n)(euler(m)(p)), -1))
                rhs = ps(euler(m + n)(p), n - m)
                check("witt_relation", lhs, rhs)
    for n in range(2, 8):
        l = lie([(1, euler(0))])
        m = lie([(n - 1, euler(1))])
        nl = lambda z, l=l: js(l(z), -1)
        nm = lambda z, m=m: js(m(z), -1)
        for p in [{1: F(1)}, {0: F(2), 1: F(1, 3), 3: F(2, 5)}]:
            f = constant(p, n)
            comm = exp_apply(l, exp_apply(m, exp_apply(nl, exp_apply(nm, f))))
            expected = constant(p, n)
            expected[n] = euler(1)(p)
            check("nonsplit_jet_witness", comm, expected)
            check("lower_jet_commutes", comm[:-1], f[:-1])
            check("upper_jet_nontrivial", comm[n] != f[n], True)


def scalar_mul(p: list[F], q: list[F], n: int) -> list[F]:
    return [sum((p[j] * q[k - j] for j in range(k + 1)), F(0))
            for k in range(n + 1)]


def square_root_checks(rng: random.Random) -> None:
    for n in range(1, 11):
        for _ in range(12):
            f = [F(0)] + [F(rng.randint(-3, 3), rng.randint(1, 4)) for _ in range(n)]
            square = scalar_mul(f, f, n)
            u = scalar_mul(square, square, n)
            u[0] += 1
            y = [F(1)] + [F(0)] * n
            for k in range(1, n + 1):
                y[k] = (u[k] - sum((y[j] * y[k - j] for j in range(1, k)), F(0))) / 2
            check("formal_square_root_recursion", scalar_mul(y, y, n), u)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "verification.json")
    args = parser.parse_args()
    rng = random.Random(20260923)
    hs_checks(rng)
    formal_checks(rng)
    commutator_checks(rng)
    square_root_checks(rng)
    report = {
        "status": "passed",
        "total_checks": sum(COUNTS.values()),
        "groups": dict(sorted(COUNTS.items())),
        "arithmetic": "fractions.Fraction (exact rational arithmetic)",
        "model": "A0 = Z + X Q[X]; finite T-jets",
        "seed": 20260923,
        "max_jet_order_exp_log": 5,
        "max_jet_order_commutator": 7,
        "max_order_square_root": 10,
        "scope": "Finite algebraic regression tests only; not a proof of surreal support, genus, class or logical claims."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
