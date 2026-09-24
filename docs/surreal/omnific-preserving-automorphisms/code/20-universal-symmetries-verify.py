#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

This program checks finite-support algebra and truncated formal identities.
It does NOT prove class existence, infinite Hahn summability, or novelty.
Only Python's standard library is required. Run with Python 3.10 or later.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from typing import Callable, Hashable, Mapping, TypeVar

E = TypeVar("E", bound=Hashable)
COUNTS: Counter[str] = Counter()
RNG = random.Random(20260923)


def check(condition: bool, group: str) -> None:
    if not condition:
        raise AssertionError(f"Failed check in {group}, after {COUNTS[group]} successes")
    COUNTS[group] += 1


def clean(p: Mapping[E, F]) -> dict[E, F]:
    return {e: F(c) for e, c in p.items() if c}


def add(p: Mapping[E, F], q: Mapping[E, F]) -> dict[E, F]:
    out = dict(p)
    for e, c in q.items():
        out[e] = out.get(e, F(0)) + c
    return clean(out)


def scale(p: Mapping[E, F], c: F) -> dict[E, F]:
    return clean({e: c * v for e, v in p.items()})


def sub(p: Mapping[E, F], q: Mapping[E, F]) -> dict[E, F]:
    return add(p, scale(q, F(-1)))


def mul(p: Mapping[E, F], q: Mapping[E, F], plus: Callable[[E, E], E]) -> dict[E, F]:
    out: dict[E, F] = {}
    for a, ca in p.items():
        for b, cb in q.items():
            e = plus(a, b)
            out[e] = out.get(e, F(0)) + ca * cb
    return clean(out)


def act(p: Mapping[E, F], transform: Callable[[E], E]) -> dict[E, F]:
    out: dict[E, F] = {}
    for a, c in p.items():
        b = transform(a)
        out[b] = out.get(b, F(0)) + c
    return clean(out)


def qplus(a: F, b: F) -> F:
    return a + b


def sig(p: Mapping[F, F], dilation: F) -> dict[F, F]:
    if dilation <= 0:
        raise ValueError("An exponent dilation must be positive")
    return act(p, lambda a: dilation * a)


def random_qpoly() -> dict[F, F]:
    out: dict[F, F] = {}
    for _ in range(RNG.randint(1, 6)):
        e = F(RNG.randint(-7, 7), RNG.randint(1, 4))
        out[e] = out.get(e, F(0)) + F(RNG.randint(-5, 5), RNG.randint(1, 4))
    return clean(out)


@dataclass(frozen=True)
class Inner:
    """Finite inner Hahn vector; sorted decreasing rational indices."""
    terms: tuple[tuple[F, F], ...] = ()

    @staticmethod
    def make(p: Mapping[F, F]) -> "Inner":
        return Inner(tuple(sorted(clean(p).items(), reverse=True)))

    @staticmethod
    def monomial(index: F, coefficient: F = F(1)) -> "Inner":
        return Inner.make({index: coefficient})

    def __add__(self, other: "Inner") -> "Inner":
        return Inner.make(add(dict(self.terms), dict(other.terms)))

    def __neg__(self) -> "Inner":
        return Inner.make(scale(dict(self.terms), F(-1)))

    def smul(self, c: F) -> "Inner":
        return Inner.make(scale(dict(self.terms), c))

    def map_indices(self, p: Callable[[F], F]) -> "Inner":
        return Inner.make(act(dict(self.terms), p))

    def sign(self) -> int:
        if not self.terms:
            return 0
        return 1 if self.terms[0][1] > 0 else -1

    def __lt__(self, other: "Inner") -> bool:
        return (self + (-other)).sign() < 0


def iplus(a: Inner, b: Inner) -> Inner:
    return a + b


def random_inner() -> Inner:
    return Inner.make(random_qpoly())


def random_outer() -> dict[Inner, F]:
    out: dict[Inner, F] = {}
    for _ in range(RNG.randint(1, 5)):
        e = random_inner()
        out[e] = out.get(e, F(0)) + F(RNG.randint(-4, 4), RNG.randint(1, 3))
    return clean(out)


def localized_index(x: F, s: F) -> F:
    """Translation by s conjugated onto (-1,1), identity outside."""
    if abs(x) >= 1:
        return x
    y = x / (1 - abs(x)) + s
    return y / (1 + abs(y))


def q_fixed(gamma: Inner) -> Inner:
    return Inner.make({a: c for a, c in gamma.terms if abs(a) >= 1})


def h_fixed(gamma: Inner) -> bool:
    return q_fixed(gamma) == gamma


def test_double_lifts() -> None:
    for _ in range(160):
        a, b = random_inner(), random_inner()
        s, t = F(RNG.randint(-4, 4), 3), F(RNG.randint(-4, 4), 2)
        trans = lambda x: x + s
        Ta = a.map_indices(trans)
        check((a + b).map_indices(trans) == Ta + b.map_indices(trans), "inner_linear_and_order")
        check(Ta.sign() == a.sign(), "inner_linear_and_order")
        check(a.map_indices(lambda x: x + t).map_indices(trans) == a.map_indices(lambda x: x + s + t), "inner_composition")
        p, q = random_outer(), random_outer()
        transform = lambda e: e.map_indices(trans)
        sp, sq = act(p, transform), act(q, transform)
        check(act(mul(p, q, iplus), transform) == mul(sp, sq, iplus), "outer_multiplication")
        check(act(add(p, q), transform) == add(sp, sq), "outer_addition")
        check(sp.get(Inner(), F(0)) == p.get(Inner(), F(0)), "outer_constant_coefficient")
        if p:
            check(sp[max(sp)] == p[max(p)], "outer_leading_coefficient")
        positive = {e: c for e, c in p.items() if e.sign() > 0}
        check(all(e.sign() > 0 for e in act(positive, transform)), "positive_support_preservation")
        locs = lambda x: localized_index(x, s)
        loct = lambda x: localized_index(x, t)
        check(a.map_indices(loct).map_indices(locs) == a.map_indices(lambda x: localized_index(x, s + t)), "localized_composition")
        check(q_fixed(a.map_indices(locs)) == q_fixed(a), "inner_fixed_projection")
        check(a.map_indices(locs).sign() == a.sign(), "localized_order")
        # Finite tests for the relative monomial part of the retraction.
        check(q_fixed(a + b) == q_fixed(a) + q_fixed(b), "relative_monomial_retraction")
        check(q_fixed(a.map_indices(locs) + (-a)) == Inner(), "relative_monomial_retraction")
        ph = {e: c for e, c in p.items() if h_fixed(e)}
        sigma_loc = act(p, lambda e: e.map_indices(locs))
        check({e: c for e, c in sigma_loc.items() if h_fixed(e)} == ph, "outer_fixed_projection")
    grid = [F(i, 5) for i in range(-12, 13)]
    for s in (F(-3), F(-1, 2), F(1, 2), F(3)):
        image = [localized_index(x, s) for x in grid]
        check(all(a < b for a, b in zip(image, image[1:])), "localized_index_order")
        for x in grid:
            check((localized_index(x, s) == x) == (abs(x) >= 1), "localized_fixed_set")


def test_green_residuals() -> None:
    for dilation in (F(2), F(3, 2), F(1, 2)):
        for c in (F(1), F(-1), F(2), F(-3, 2), F(1, 3)):
            for nterms in (1, 2, 3, 5, 8):
                for _ in range(7):
                    f = random_qpoly()
                    fplus = {e: a for e, a in f.items() if dilation * e > e}
                    fminus = {e: a for e, a in f.items() if dilation * e < e}
                    xp: dict[F, F] = {}
                    xm: dict[F, F] = {}
                    for n in range(1, nterms + 1):
                        xp = add(xp, scale(sig(fplus, dilation ** (-n)), c ** (n - 1)))
                    for n in range(nterms):
                        xm = add(xm, scale(sig(fminus, dilation ** n), -(c ** (-n - 1))))
                    lhs_p = sub(sig(xp, dilation), scale(xp, c))
                    rhs_p = sub(fplus, scale(sig(fplus, dilation ** (-nterms)), c ** nterms))
                    lhs_m = sub(sig(xm, dilation), scale(xm, c))
                    rhs_m = sub(fminus, scale(sig(fminus, dilation ** nterms), c ** (-nterms)))
                    check(lhs_p == rhs_p, "weighted_green_positive_residual")
                    check(lhs_m == rhs_m, "weighted_green_negative_residual")
                    x = add(xp, xm)
                    if c != 1:
                        x = add(x, {F(0): f.get(F(0), F(0)) / (1 - c)})
                        tails = add(scale(sig(fplus, dilation ** (-nterms)), c ** nterms),
                                    scale(sig(fminus, dilation ** nterms), c ** (-nterms)))
                        check(sub(sig(x, dilation), scale(x, c)) == sub(f, tails), "constant_plus_tail_residual")


def test_orbit_independence() -> None:
    # Finite polynomial monomials in outer omega^(inner basis vector).
    for shift in (F(0), F(1, 3), F(-5, 2)):
        basis = [Inner.monomial(shift + j) for j in range(4)]
        seen: set[Inner] = set()
        for powers in itertools.product(range(4), repeat=4):
            exponent = Inner()
            for b, n in zip(basis, powers):
                exponent = exponent + b.smul(F(n))
            check(exponent not in seen, "distinct_outer_polynomial_exponents")
            seen.add(exponent)
    # Relative cosets: inside-interval basis differences have no fixed projection.
    inside = [Inner.monomial(F(i, 5)) for i in (-2, 0, 3)]
    for powers in itertools.product(range(3), repeat=3):
        v = Inner()
        for b, n in zip(inside, powers):
            v = v + b.smul(F(n))
        check(q_fixed(v) == Inner(), "relative_independence_projection")
        check((v == Inner()) == (not any(powers)), "relative_independence_nonzero")


@dataclass
class Rat:
    """Rational function of finite Hahn polynomials; equality by cross products."""
    num: dict[F, F]
    den: dict[F, F]

    def __post_init__(self) -> None:
        self.num, self.den = clean(self.num), clean(self.den)
        if not self.den:
            raise ZeroDivisionError("Zero rational-function denominator")

    def __mul__(self, other: "Rat") -> "Rat":
        return Rat(mul(self.num, other.num, qplus), mul(self.den, other.den, qplus))

    def equivalent(self, other: "Rat") -> bool:
        return mul(self.num, other.den, qplus) == mul(other.num, self.den, qplus)

    def sigma(self, dilation: F) -> "Rat":
        return Rat(sig(self.num, dilation), sig(self.den, dilation))

    def leading_coefficient(self) -> F:
        if not self.num:
            raise ValueError("Zero has no leading coefficient")
        return self.num[max(self.num)] / self.den[max(self.den)]


def test_gauge_and_cocycles() -> None:
    for _ in range(140):
        u, y, m = random_qpoly(), random_qpoly(), random_qpoly()
        if not u:
            u = {F(0): F(1)}
        dilation = RNG.choice((F(2), F(3), F(1, 2)))
        c = RNG.choice((F(-1), F(1), F(2), F(1, 3)))
        su, sy = sig(u, dilation), sig(y, dilation)
        # sigma(uy) - c*sigma(u)*y = sigma(u)*(sigma(y)-c*y).
        left = sub(sig(mul(u, y, qplus), dilation), scale(mul(su, y, qplus), c))
        right = mul(su, sub(sy, scale(y, c)), qplus)
        check(left == right, "cleared_denominator_gauge_identity")
        n, r = RNG.randint(-3, 3), RNG.randint(-3, 3)
        h = F(RNG.randint(-3, 3), 2)
        def additive_cocycle(j: int) -> dict[F, F]:
            return add(sub(sig(m, dilation ** j), m), {F(0): j * h})
        check(additive_cocycle(n + r) == add(additive_cocycle(n), sig(additive_cocycle(r), dilation ** n)), "additive_cocycle_identity")
        char = RNG.choice((F(2), F(3, 2), F(-1)))
        def multiplicative_cocycle(j: int) -> Rat:
            return Rat(scale(sig(u, dilation ** j), char ** j), u)
        a = multiplicative_cocycle(n + r)
        b = multiplicative_cocycle(n) * multiplicative_cocycle(r).sigma(dilation ** n)
        check(a.equivalent(b), "multiplicative_cocycle_identity")
        check(multiplicative_cocycle(n).leading_coefficient() == char ** n, "multiplicative_character_extraction")
        f1, f2 = sub(sig(m, F(2)), m), sub(sig(m, F(3)), m)
        check(sub(sig(f2, F(2)), f2) == sub(sig(f1, F(3)), f1), "commuting_difference_compatibility")


def trunc(p: Mapping[int, F], degree: int) -> dict[int, F]:
    return {n: c for n, c in clean(p).items() if n <= degree}


def tmul(p: Mapping[int, F], q: Mapping[int, F], degree: int) -> dict[int, F]:
    return trunc(mul(p, q, lambda a, b: a + b), degree)


def formal_log(u: Mapping[int, F], degree: int) -> dict[int, F]:
    if u.get(0, F(0)) != 1:
        raise ValueError("Formal logarithm requires constant coefficient one")
    eps = sub(u, {0: F(1)})
    out: dict[int, F] = {}
    power = {0: F(1)}
    for n in range(1, degree + 1):
        power = tmul(power, eps, degree)
        out = add(out, scale(power, F((-1) ** (n + 1), n)))
    return out


def formal_exp(h: Mapping[int, F], degree: int) -> dict[int, F]:
    if h.get(0, F(0)) != 0:
        raise ValueError("Formal exponential requires zero constant coefficient")
    out = {0: F(1)}
    term = {0: F(1)}
    for n in range(1, degree + 1):
        term = scale(tmul(term, h, degree), F(1, n))
        out = add(out, term)
    return out


def test_formal_units() -> None:
    for degree in (3, 5, 8, 12):
        for _ in range(14):
            eps = clean({n: F(RNG.randint(-3, 3), RNG.randint(1, 3)) for n in range(1, 4)})
            eta = clean({n: F(RNG.randint(-3, 3), RNG.randint(1, 3)) for n in range(1, 4)})
            u, v = add({0: F(1)}, eps), add({0: F(1)}, eta)
            check(formal_exp(formal_log(u, degree), degree) == trunc(u, degree), "truncated_exp_log_inverse")
            check(formal_log(formal_exp(eps, degree), degree) == trunc(eps, degree), "truncated_log_exp_inverse")
            check(formal_log(tmul(u, v, degree), degree) == add(formal_log(u, degree), formal_log(v, degree)), "truncated_log_product")
            sigma_u = trunc(act(u, lambda n: 2 * n), degree)
            sigma_log = trunc(act(formal_log(u, degree), lambda n: 2 * n), degree)
            check(formal_log(sigma_u, degree) == sigma_log, "truncated_log_sigma_commutation")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    test_double_lifts()
    test_green_residuals()
    test_orbit_independence()
    test_gauge_and_cocycles()
    test_formal_units()
    report = {
        "status": "PASS",
        "arithmetic": "fractions.Fraction (exact rational arithmetic)",
        "seed": 20260923,
        "total_assertions": sum(COUNTS.values()),
        "check_groups": dict(sorted(COUNTS.items())),
        "scope": [
            "Finite inner and outer Hahn lifts, including localized index actions",
            "Weighted finite Green residual identities for both orbit directions",
            "Finite independent-exponent and relative-projection tests",
            "Cleared-denominator gauge and cocycle identities",
            "Truncated formal logarithm and exponential identities"
        ],
        "not_verified": [
            "Infinite Hahn summability and arbitrary supports",
            "Class recursion, eta_On order isomorphism, or global choice arguments",
            "Any full theorem by a proof assistant",
            "Originality, priority, or exhaustive repository nonduplication"
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
