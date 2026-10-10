#!/usr/bin/env python3
"""Reproduce exact algebra, rational enclosures, and numerical diagnostics.

The all-n optimality theorem is analytic. This program checks its algebra
independently and certifies finite sample values with integer arithmetic.
No floating point number is used in an exact certificate. mpmath output
is separately labelled diagnostic. Run with Python 3, SymPy, and mpmath.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


PRECISION = 120
SCALE = 10**PRECISION


def ceil_div(a: int, b: int) -> int:
    assert b > 0
    return -((-a) // b)


@dataclass(frozen=True)
class Interval:
    """Closed rational interval [lo/SCALE, hi/SCALE]."""

    lo: int
    hi: int

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def exact(x: int | Fraction) -> "Interval":
        q = Fraction(x)
        return Interval(
            q.numerator * SCALE // q.denominator,
            ceil_div(q.numerator * SCALE, q.denominator),
        )

    def __add__(self, other):
        b = other if isinstance(other, Interval) else Interval.exact(other)
        return Interval(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, Interval) else -Fraction(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        b = other if isinstance(other, Interval) else Interval.exact(other)
        products = [self.lo * b.lo, self.lo * b.hi,
                    self.hi * b.lo, self.hi * b.hi]
        return Interval(min(products) // SCALE, ceil_div(max(products), SCALE))

    __rmul__ = __mul__

    def divide_integer(self, k: int):
        assert k > 0
        return Interval(self.lo // k, ceil_div(self.hi, k))

    def reciprocal(self):
        assert self.lo > 0
        return Interval(SCALE * SCALE // self.hi,
                        ceil_div(SCALE * SCALE, self.lo))


def exp_negative(x: Interval) -> Interval:
    """Enclose exp(x) for x <= 0 by positive Taylor sum, inversion, squaring.

After reduction t in [0,1], the omitted exp(t) tail after degree M
is <= 2/(M+1)!. All interval operations round outward using integers.
"""
    assert x.hi <= 0
    u = -x
    squarings = 0
    while u.hi > SCALE:
        u = u.divide_integer(2)
        squarings += 1
    total = term = Interval.exact(1)
    degree = 100
    for j in range(1, degree + 1):
        term = (term * u).divide_integer(j)
        total = total + term
    tail = ceil_div(2 * SCALE, math.factorial(degree + 1))
    total = Interval(total.lo, total.hi + tail)
    value = total.reciprocal()
    for _ in range(squarings):
        value = value * value
    return value


def exp_positive(x: Interval) -> Interval:
    assert x.lo >= 0
    return exp_negative(-x).reciprocal()


def fraction_text(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def decimal_enclosure(x: Interval, places: int = 20) -> list[str]:
    unit = 10**places
    low = x.lo * unit // SCALE
    high = ceil_div(x.hi * unit, SCALE)

    def fmt(v: int) -> str:
        sign = "-" if v < 0 else ""
        v = abs(v)
        return f"{sign}{v // unit}.{v % unit:0{places}d}"

    return [fmt(low), fmt(high)]


def cubic(n: int, r: Fraction) -> Fraction:
    return r**3 + n * r**2 - n * r - n


def isolate_r(n: int) -> tuple[Fraction, Fraction]:
    lo, hi = Fraction(1), Fraction(2)
    for _ in range(410):
        mid = (lo + hi) / 2
        if cubic(n, mid) < 0:
            lo = mid
        else:
            hi = mid
    assert cubic(n, lo) < 0 < cubic(n, hi)
    return lo, hi


def interval_from_bounds(lo: Fraction, hi: Fraction) -> Interval:
    return Interval(Interval.exact(lo).lo, Interval.exact(hi).hi)


def R_interval(n: int, y: Fraction, r: Interval) -> Interval:
    t = Interval.exact(y)
    poly = 2 * t * t - 3 * n * t + n * (n - 1)
    exponential = exp_negative(t - n - r)
    return poly + (2 - r) * exponential * t * (n - t)


def certify(n: int) -> dict:
    rl, rh = isolate_r(n)
    r = interval_from_bounds(rl, rh)
    lo, hi = Fraction(0), Fraction(n - 1, 2)
    assert R_interval(n, lo, r).lo > 0
    assert R_interval(n, hi, r).hi < 0
    for _ in range(130):
        mid = (lo + hi) / 2
        value = R_interval(n, mid, r)
        if value.lo > 0:
            lo = mid
        elif value.hi < 0:
            hi = mid
        else:
            raise ArithmeticError("Insufficient integer interval precision")
    lower_sign = R_interval(n, lo, r)
    upper_sign = R_interval(n, hi, r)
    assert lower_sign.lo > 0 and upper_sign.hi < 0
    eta = interval_from_bounds(lo, hi)
    tau = (2 - r) * exp_negative(-r)
    lam = (2 - r) * exp_negative(-n - r)
    cutoff = exp_positive(eta)
    return {
        "n": n,
        "status": "exact rational interval certificate",
        "r_interval": [fraction_text(rl), fraction_text(rh)],
        "eta_interval": [fraction_text(lo), fraction_text(hi)],
        "cubic_endpoint_signs": [-1, 1],
        "R_endpoint_signs": [1, -1],
        "r_decimal_enclosure": decimal_enclosure(r),
        "eta_decimal_enclosure": decimal_enclosure(eta),
        "tau_decimal_enclosure": decimal_enclosure(tau),
        "lambda_decimal_enclosure": decimal_enclosure(lam, 70),
        "cutoff_decimal_enclosure": decimal_enclosure(cutoff),
    }


def check_symbolic() -> dict:
    import sympy as s

    n, r, y, tau, eps = s.symbols("n r y tau eps")
    T = 2 - (n - 1) / (n + r) - 1 / r
    p = r**3 + n * r**2 - n * r - n
    R = 2 * y**2 - 3 * n * y + n * (n - 1) + tau * s.exp(y - n) * y * (n - y)
    checks = {}

    def identity(name, expr):
        assert s.simplify(expr) == 0, name
        checks[name] = True

    identity("tail_critical_cubic_factor",
             (T - s.diff(T, r)) * r**2 * (n + r)**2 - (n + 2 * r) * p)
    identity("critical_value_reduction", (T - (2 - r)) * r * (n + r) - p)
    identity("positive_cutoff_second_derivative", s.diff(R, y, 2) - 4
             - tau * s.exp(y - n) * (-y**2 + (n - 4) * y + 2 * n - 2))
    identity("cubic_discriminant", s.discriminant(eps * r**3 + r**2 - r - 1, r)
             - (1 - eps) * (27 * eps + 5))
    identity("index_as_function_of_r_derivative",
             s.diff(r**3 / (1 + r - r**2), r)
             - r**2 * (3 + 2 * r - r**2) / (1 + r - r**2)**2)
    phi = (1 + s.sqrt(5)) / 2
    r1 = -1 - 2 * s.sqrt(5) / 5
    r2 = s.Rational(5, 2) + 57 * s.sqrt(5) / 50
    series_r = phi + r1 * eps + r2 * eps**2
    polynomial = s.expand(eps * series_r**3 + series_r**2 - series_r - 1)
    for j in range(3):
        identity(f"r_asymptotic_coefficient_{j}", polynomial.coeff(eps, j))
    ratio = (2 - series_r) * s.exp(phi - series_r) / (2 - phi)
    identity("tau_first_correction", s.diff(ratio, eps).subs(eps, 0)
             - (7 + 3 * s.sqrt(5)) / 2)
    identity("tau_second_correction", s.diff(ratio, eps, 2).subs(eps, 0) / 2
             + (35 + 16 * s.sqrt(5)) / 10)
    return {"status": "exact symbolic identities", "checks": checks,
            "count": len(checks)}


def diagnostics() -> list[dict]:
    import mpmath as mp

    mp.mp.dps = 100
    phi = (1 + mp.sqrt(5)) / 2
    result = []
    for n in [2, 3, 4, 5, 10, 25, 100]:
        r = mp.findroot(lambda z: z**3 + n * z**2 - n * z - n, (1, phi))
        tau = (2 - r) * mp.exp(-r)
        delta = mp.sqrt(n * n + 8 * n)
        alpha = (3 * n - delta) / 4

        def cutoff(t):
            low, high = alpha, mp.mpf(n - 1) / 2
            for _ in range(310):
                z = (low + high) / 2
                val = 2 * z*z - 3*n*z + n*(n-1) + t*mp.exp(z-n)*z*(n-z)
                if val > 0:
                    low = z
                else:
                    high = z
            return (low + high) / 2

        eta, old_eta = cutoff(tau), cutoff(1)
        vals = {"r": r, "tau": tau, "eta": eta, "cutoff": mp.exp(eta),
                "fixed_coefficient_cutoff": mp.exp(old_eta),
                "first_stationary_point": mp.exp(alpha),
                "additive_displacement": mp.exp(eta)-mp.exp(alpha),
                "cutoff_improvement": mp.exp(old_eta)-mp.exp(eta)}
        result.append({"n": n, "status": "100-digit non-interval diagnostics",
                       **{k: mp.nstr(v, 65) for k, v in vals.items()}})
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1]/"data"/"optimal_barrier_verification.json")
    args = parser.parse_args()
    data = {"symbolic": check_symbolic(),
            "exact_interval_method": {
                "scale_digits": PRECISION,
                "exponential_degree": 100,
                "exponential_tail": "2/(M+1)! on [0,1]; then inversion and squaring",
                "root_isolation": "exact cubic bisection; certified R signs with outward integer arithmetic",
            },
            "certificates": [certify(n) for n in [2, 3, 4, 5, 10, 25, 100]],
            "diagnostics": diagnostics()}
    args.output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"Verified {data['symbolic']['count']} symbolic identities and "
          f"{len(data['certificates'])} exact optimizer/cutoff enclosures.")
    print(f"Output: {args.output}")


if __name__ == "__main__":
    main()
