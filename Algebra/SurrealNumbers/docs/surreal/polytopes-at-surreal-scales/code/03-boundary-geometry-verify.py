#!/usr/bin/env python3
"""Exact finite checks for Infinitesimal Boundary Geometry of Surreal Polytopes.

Python 3.10+, standard library only. No floating-point arithmetic is used in
any assertion. Finite tests support examples; they do not prove the general
theorems or certify the analytic natural-boundary conclusion.
"""
from __future__ import annotations

import argparse
import csv
import json
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt
from pathlib import Path


@dataclass(frozen=True)
class Q2:
    """An exact element a + b*sqrt(2)."""
    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    @staticmethod
    def lift(x: Q2 | int | Fraction) -> Q2:
        return x if isinstance(x, Q2) else Q2(Fraction(x))

    def __add__(self, other: Q2 | int | Fraction) -> Q2:
        y = Q2.lift(other)
        return Q2(self.a + y.a, self.b + y.b)

    __radd__ = __add__

    def __neg__(self) -> Q2:
        return Q2(-self.a, -self.b)

    def __sub__(self, other: Q2 | int | Fraction) -> Q2:
        return self + (-Q2.lift(other))

    def __rsub__(self, other: Q2 | int | Fraction) -> Q2:
        return Q2.lift(other) + (-self)

    def __mul__(self, other: Q2 | int | Fraction) -> Q2:
        y = Q2.lift(other)
        return Q2(self.a*y.a + 2*self.b*y.b, self.a*y.b + self.b*y.a)

    __rmul__ = __mul__

    def sign(self) -> int:
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a == 0:
            return (b > 0) - (b < 0)
        if (a > 0) == (b > 0):
            return 1 if a > 0 else -1
        diff = a*a - 2*b*b
        assert diff != 0  # sqrt(2) is irrational, a and b are nonzero rationals.
        return ((a > 0) - (a < 0)) * ((diff > 0) - (diff < 0))


@dataclass(frozen=True)
class EP:
    """Polynomial in a positive infinitesimal, coefficients in Q(sqrt(2))."""
    coeffs: tuple[Q2, ...]

    @staticmethod
    def lift(x: EP | Q2 | int | Fraction) -> EP:
        return x if isinstance(x, EP) else EP((Q2.lift(x),))

    def __add__(self, other: EP | Q2 | int | Fraction) -> EP:
        y = EP.lift(other)
        n = max(len(self.coeffs), len(y.coeffs))
        return EP(tuple((self.coeffs[i] if i < len(self.coeffs) else Q2()) +
                        (y.coeffs[i] if i < len(y.coeffs) else Q2())
                        for i in range(n)))

    __radd__ = __add__

    def __neg__(self) -> EP:
        return EP(tuple(-x for x in self.coeffs))

    def __sub__(self, other: EP | Q2 | int | Fraction) -> EP:
        return self + (-EP.lift(other))

    def __rsub__(self, other: EP | Q2 | int | Fraction) -> EP:
        return EP.lift(other) + (-self)

    def __mul__(self, other: EP | Q2 | int | Fraction) -> EP:
        y = EP.lift(other)
        out = [Q2() for _ in range(len(self.coeffs) + len(y.coeffs) - 1)]
        for i, a in enumerate(self.coeffs):
            for j, b in enumerate(y.coeffs):
                out[i+j] = out[i+j] + a*b
        return EP(tuple(out))

    __rmul__ = __mul__

    def sign(self) -> int:
        for a in self.coeffs:
            if a.sign():
                return a.sign()
        return 0


def ceil_n_over_sqrt(n: int, m: int) -> int:
    """ceil(n/sqrt(m)) for positive nonsquare integer m and n >= 0."""
    if n < 0 or m < 2 or isqrt(m)**2 == m:
        raise ValueError("Require n >= 0 and nonsquare m >= 2")
    if n == 0:
        return 0
    c = isqrt(n*n // m) + 1
    assert m*(c-1)**2 < n*n < m*c*c
    return c


def quad_formula(n: int) -> int:
    return (n+1)**2 - ceil_n_over_sqrt(n, 2)


def quad_contains(n: int, x: int, y: int) -> bool:
    """Exact lexicographic membership of (x,y) in n P_(1/sqrt(2),eps)."""
    if not (0 <= x <= n and y >= 0):
        return False
    slack0 = n-y
    if slack0 != 0:
        return slack0 > 0
    return 2*x*x >= n*n


def check_geometry() -> dict:
    alpha = Q2(Fraction(0), Fraction(1, 2))
    e = EP((Q2(), Q2(Fraction(1))))
    zero, one = EP.lift(0), EP.lift(1)
    vertices = [(zero, zero), (one, zero),
                (one, one + e*(1-alpha)), (zero, one - e*alpha)]
    expected_zero_rows = [{0, 2}, {1, 2}, {1, 3}, {0, 3}]
    slack_tests = 0
    for (x, y), expected in zip(vertices, expected_zero_rows):
        slacks = [x, 1-x, y, 1 + e*(x-alpha)-y]
        actual = {i for i, s in enumerate(slacks) if s.sign() == 0}
        assert actual == expected
        assert all(s.sign() >= 0 for s in slacks)
        slack_tests += len(slacks)
    for i in range(4):
        a, b, c = vertices[i], vertices[(i+1) % 4], vertices[(i+2) % 4]
        determinant = (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])
        assert determinant.sign() > 0
    twice_area = EP.lift(0)
    for i in range(4):
        a, b = vertices[i], vertices[(i+1) % 4]
        twice_area += a[0]*b[1] - a[1]*b[0]
    assert (twice_area - (2 + e*(1-2*alpha))).sign() == 0
    return {"vertex_facet_slacks": slack_tests, "positive_turns": 4,
            "shoelace_identity": "2 area = 2 + eps*(1 - sqrt(2))"}


def run(out_dir: Path) -> dict:
    geometry = check_geometry()
    lattice_candidates = 0
    for n in range(1, 151):
        direct = 0
        for x in range(-1, n+2):
            for y in range(-1, n+2):
                direct += quad_contains(n, x, y)
                lattice_candidates += 1
        assert direct == quad_formula(n), (n, direct, quad_formula(n))
    for n in range(1, 10001):
        c = ceil_n_over_sqrt(n, 2)
        assert 0 <= c <= n
        assert c-ceil_n_over_sqrt(n-1, 2) in (0, 1)
        assert quad_formula(n) == n*(n+1) + n+1-c

    rational_tests = 0
    for q in range(2, 13):
        for p in range(1, q):
            for n in range(1, 61):
                c = (p*n + q-1)//q
                direct_top = sum(q*x >= p*n for x in range(n+1))
                value = n*(n+1)+direct_top
                assert value == (n+1)**2-c
                # On a residue class modulo q, the third forward difference is zero.
                vals = [Fraction((n+k*q+1)**2 - (p*(n+k*q)+q-1)//q)
                        for k in range(4)]
                assert vals[3]-3*vals[2]+3*vals[1]-vals[0] == 0
                rational_tests += 1

    cube_candidates = 0
    for n in range(1, 36):
        direct = 0
        for x in range(n+1):
            for y in range(n+1):
                for z in range(n+1):
                    direct += (z < n or (2*x*x >= n*n and 3*y*y >= n*n))
                    cube_candidates += 1
        top = (n+1-ceil_n_over_sqrt(n, 2))*(n+1-ceil_n_over_sqrt(n, 3))
        assert direct == n*(n+1)**2+top

    # An exact, finite demonstration of pointwise real specialization.
    # Each t is selected for this particular n; no uniform t is claimed.
    specialization_checks = 0
    alpha = Q2(Fraction(0), Fraction(1, 2))
    for n in range(1, 101):
        t = Fraction(1, 4*(n+1))
        real_count = 0
        for x in range(n+1):
            for y in range(n+2):
                slack = Q2(Fraction(n-y)) + (Q2(Fraction(x))-alpha*n)*t
                real_count += slack.sign() >= 0
                specialization_checks += 1
        assert real_count == quad_formula(n)

    result = {
        "status": "all exact assertions passed",
        "arithmetic": "integers, Fraction, exact Q(sqrt(2)), lexicographic polynomials",
        "quad_geometry": geometry,
        "quad_direct_dilations": [1, 150],
        "quad_direct_lattice_candidates": lattice_candidates,
        "quad_formula_and_increment_dilations": [1, 10000],
        "rational_threshold_cases": rational_tests,
        "cube_implantation_direct_dilations": [1, 35],
        "cube_lattice_candidates": cube_candidates,
        "pointwise_specialization_dilations": [1, 100],
        "pointwise_specialization_candidates": specialization_checks,
        "pointwise_specialization_rule": "t_n = 1 / (4*(n+1)); varies with n",
        "not_verified_by_this_script": [
            "the general trace and descent theorems",
            "the surface coefficient and full-interval realization theorems",
            "non-quasipolynomiality for infinitely many n",
            "natural boundary and non-P-recursiveness",
            "any Lean proof or repository build"
        ]
    }
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "verification.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    with (out_dir / "counts.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "ceil_n_over_sqrt2", "L_quad", "L_square", "removed_top_points"])
        for n in range(101):
            c = ceil_n_over_sqrt(n, 2)
            writer.writerow([n, c, quad_formula(n), (n+1)**2, c])
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    print(json.dumps(run(args.out_dir), indent=2))
