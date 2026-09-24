#!/usr/bin/env python3
"""Exact finite checks for the genetic-gap research note.

Python 3.9+, standard library only.  This is NOT a surreal-number kernel and
NOT a formal proof of a statement quantified over all surreal numbers.
It checks algebra in Q(t), ordered with t larger than every rational, and
finite Conway-cut examples.  The infinitary proof is in article.tex.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as F
from functools import total_ordering
from itertools import combinations
import json
from pathlib import Path
import random
import sys
from typing import Dict, Iterable, Tuple, Union

Poly = Tuple[F, ...]
Scalar = Union[int, F]


def trim(p: Iterable[Scalar]) -> Poly:
    values = [F(x) for x in p]
    while values and not values[-1]:
        values.pop()
    return tuple(values)


def padd(a: Poly, b: Poly) -> Poly:
    return trim((a[i] if i < len(a) else F(0)) +
                (b[i] if i < len(b) else F(0))
                for i in range(max(len(a), len(b))))


def pneg(a: Poly) -> Poly:
    return tuple(-x for x in a)


def pmul(a: Poly, b: Poly) -> Poly:
    if not a or not b:
        return ()
    result = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return trim(result)


@total_ordering
class Rat:
    """Rational function, ordered by its eventual sign as t tends to +infinity.

    GCD reduction is unnecessary: equality is checked by cross multiplication.
    Denominators have positive leading coefficient, not necessarily positive
    values at each real argument.  They ARE positive in this ordered field.
    """
    __slots__ = ("num", "den")

    def __init__(self, num: Iterable[Scalar] = (), den: Iterable[Scalar] = (1,)):
        self.num = trim(num)
        self.den = trim(den)
        if not self.den:
            raise ZeroDivisionError("zero polynomial denominator")
        scale = self.den[-1]
        self.num = tuple(x / scale for x in self.num)
        self.den = tuple(x / scale for x in self.den)

    @staticmethod
    def coerce(value: Union['Rat', Scalar]) -> 'Rat':
        return value if isinstance(value, Rat) else Rat((F(value),))

    def __add__(self, other: Union['Rat', Scalar]) -> 'Rat':
        b = self.coerce(other)
        return Rat(padd(pmul(self.num, b.den), pmul(b.num, self.den)),
                   pmul(self.den, b.den))

    __radd__ = __add__

    def __neg__(self) -> 'Rat':
        return Rat(pneg(self.num), self.den)

    def __sub__(self, other: Union['Rat', Scalar]) -> 'Rat':
        return self + -self.coerce(other)

    def __rsub__(self, other: Union['Rat', Scalar]) -> 'Rat':
        return self.coerce(other) + -self

    def __mul__(self, other: Union['Rat', Scalar]) -> 'Rat':
        b = self.coerce(other)
        return Rat(pmul(self.num, b.num), pmul(self.den, b.den))

    __rmul__ = __mul__

    def __truediv__(self, other: Union['Rat', Scalar]) -> 'Rat':
        b = self.coerce(other)
        return Rat(pmul(self.num, b.den), pmul(self.den, b.num))

    def __rtruediv__(self, other: Union['Rat', Scalar]) -> 'Rat':
        return self.coerce(other) / self

    def sign(self) -> int:
        return 0 if not self.num else (1 if self.num[-1] > 0 else -1)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, (Rat, int, F)):
            return NotImplemented
        b = self.coerce(other)
        return pmul(self.num, b.den) == pmul(b.num, self.den)

    def __lt__(self, other: Union['Rat', Scalar]) -> bool:
        return (self - self.coerce(other)).sign() < 0

    def __abs__(self) -> 'Rat':
        return -self if self.sign() < 0 else self

    def infinite_positive(self) -> bool:
        return self.sign() > 0 and len(self.num) > len(self.den)

    def finite(self) -> bool:
        return not self.num or len(self.num) <= len(self.den)

    def natural_upper_witness(self) -> int:
        """Return an explicit n with x <= n when x is not positive infinite."""
        if self.infinite_positive():
            raise ValueError("no natural upper bound")
        if self <= 0:
            return 0
        if len(self.num) < len(self.den):
            return 1
        limit = self.num[-1] / self.den[-1]
        return max(1, limit.numerator // limit.denominator + 2)

    def display(self) -> str:
        def fmt(p: Poly) -> str:
            return " + ".join(f"({c})*t^{i}" for i, c in enumerate(p) if c) or "0"
        return f"({fmt(self.num)}) / ({fmt(self.den)})"


def q(x: Rat) -> Rat:
    return x / (1 + x * x)


def indicator(x: Rat) -> int:
    """Exact degree classification in Q(t), NOT a finite test of all naturals."""
    return int(x.infinite_positive())


def shift(x: Rat, c: Union[Rat, Scalar] = -1) -> Rat:
    return x + Rat.coerce(c) * indicator(x)


def dyadic_birth(x: F) -> int:
    """Birthday of a finite dyadic rational in Conway's canonical tree."""
    if x.denominator & (x.denominator - 1):
        raise ValueError("not dyadic")
    if x.denominator == 1:
        return abs(x.numerator)
    return abs(x.numerator) // x.denominator + 1 + x.denominator.bit_length() - 1


def finite_simplest_above(options: Iterable[F]) -> F:
    """Brute-force the early dyadic tree; inputs here lie strictly below 1."""
    opts = tuple(options)
    candidates = {F(i, 2 ** k) for k in range(6)
                  for i in range(-4 * 2 ** k, 4 * 2 ** k + 1)}
    valid = [v for v in candidates if all(a < v for a in opts)]
    if not valid:
        raise ValueError("search window too small")
    youngest = min(dyadic_birth(v) for v in valid)
    winners = [v for v in valid if dyadic_birth(v) == youngest]
    if len(winners) != 1:
        raise AssertionError("minimal birthday was not unique in test window")
    return winners[0]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        "results" / "verification.json")
    args = parser.parse_args()
    counts: Dict[str, int] = defaultdict(int)

    def check(group: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(f"failed: {group}, after {counts[group]} successes")
        counts[group] += 1

    zero, one, t = Rat(), Rat((1,)), Rat((0, 1))
    # Boundary cases chosen independently of the pseudorandom sample.
    named = {
        "0": zero, "1": one, "-1": -one, "t": t, "-t": -t,
        "1/t": 1/t, "-1/t": -1/t, "t-1": t-1, "t/2": t/2,
        "1+1/t": 1+1/t, "t/(t+1)": t/(t+1), "t^2": t*t,
        "t^2-t": t*t-t, "-t^2+t": -t*t+t,
    }
    rng = random.Random(20260920)
    sample = list(named.values())
    for _ in range(70):
        numerator = [F(rng.randint(-6, 6), rng.randint(1, 5))
                     for _ in range(rng.randint(1, 5))]
        denominator = [F(rng.randint(-6, 6), rng.randint(1, 5))
                       for _ in range(rng.randint(1, 5))]
        if not trim(denominator):
            denominator = [F(1)]
        sample.append(Rat(numerator, denominator))

    for x in sample:
        check("field_identities", (x + 1) - 1 == x)
        check("field_identities", x - x == 0)
        check("field_identities", x * (x + 1) == x*x+x)
        if x != 0:
            check("field_identities", x/x == 1)
        check("rational_sign_and_bounds", (1 + x*x) > 0)
        check("rational_sign_and_bounds", q(x).sign() == x.sign())
        check("rational_sign_and_bounds", abs(q(x)) <= F(1, 2))
        check("rational_sign_and_bounds", -1 < q(x) < 1)
        check("square_certificates", 1+x*x-x == (x-F(1, 2))*(x-F(1, 2))+F(3, 4))
        check("square_certificates", 1+x*x+x == (x+F(1, 2))*(x+F(1, 2))+F(3, 4))
        if not x.infinite_positive():
            n = x.natural_upper_witness()
            check("natural_upper_witnesses", x <= n)
            check("natural_upper_witnesses", q(n-x) >= 0)
        else:
            for n in (0, 1, 2, 10, 1000):
                check("infinite_option_sign_samples", q(n-x) < 0)
        check("inverse_maps", shift(shift(x, -1), 1) == x)
        check("inverse_maps", shift(shift(x, 1), -1) == x)

    shifts = [Rat((F(-3, 4),)), Rat((F(2, 3),)), 1/t, -1/t,
              1/(t*t), (t+1)/(2*t+3)]
    for h in shifts:
        check("punctured_neighborhoods", 0 < abs(h) < 1)
        for x in sample:
            check("local_constancy", indicator(x+h) == indicator(x))
            # Check exact numerator identity, then the quotient identity.
            check("derivative_quotients", shift(x+h) - shift(x) == h)
            check("derivative_quotients", (shift(x+h)-shift(x))/h == 1)
            check("indicator_quotients", Rat((indicator(x+h)-indicator(x),))/h == 0)

    for x, y in combinations(sample, 2):
        if x != y:
            check("order_automorphism", (shift(x) < shift(y)) == (x < y))

    finite_constants = [Rat((F(3, 2),)), -2+1/t, 1/t]
    for c in finite_constants:
        for d in finite_constants:
            for x in sample[:20]:
                check("finite_shift_group", shift(shift(x, d), c) == shift(x, c+d))

    rational_points = [F(j, 4) for j in range(-12, 33)]
    for cutoff in range(6):
        for x in rational_points:
            opts = [(F(n)-x)/(1+(F(n)-x)**2) for n in range(cutoff+1)]
            actual = finite_simplest_above(opts)
            check("finite_conway_cuts", actual == (1 if x <= cutoff else 0))

    # Rational-function witnesses to the first eight ordinal-scale indicators.
    for j in range(8):
        x = Rat([0] * (j+1) + [1])
        for i in range(8):
            scale = Rat([0] * i + [1])
            check("triangular_scale_matrix", indicator(x/scale) == int(i <= j))

    report = {
        "status": "PASS", "seed": 20260920,
        "python_version": sys.version.split()[0],
        "dependencies": "Python standard library only",
        "sample_rational_functions": len(sample),
        "checks_by_group": dict(sorted(counts.items())),
        "total_checks": sum(counts.values()),
        "named_examples": [{"x": name, "B(x)": indicator(x),
                            "F(x)": shift(x).display()}
                           for name, x in named.items()],
        "scope": [
            "Exact finite computations in the ordered rational-function field Q(t).",
            "Exact early-day dyadic Conway-cut searches with rational option values.",
            "The positive-infinite classification is by polynomial degree and sign.",
            "The program does not simulate all surreal numbers or prove genetic admissibility.",
            "Finite option samples are not evidence for a universal natural-number quantifier.",
            "The general proofs, including the countable cut, are in article.tex."
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in
                      ("status", "sample_rational_functions", "total_checks", "checks_by_group")},
                     indent=2))


if __name__ == "__main__":
    main()
