#!/usr/bin/env python3
"""Exact rational checks of all strict exponent inequalities in Section 3.

This script does not replace the analytic proof. It certifies the
parameter comparisons used in that proof with rational atanh-series
intervals; no floating-point arithmetic occurs in verification.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path


@dataclass(frozen=True)
class Interval:
    lower: F
    upper: F

    def __post_init__(self):
        if self.lower > self.upper:
            raise ValueError("reversed interval")

    def __add__(self, other):
        other = as_interval(other)
        return Interval(self.lower + other.lower, self.upper + other.upper)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.upper, -self.lower)

    def __sub__(self, other):
        return self + (-as_interval(other))

    def __rsub__(self, other):
        return as_interval(other) - self

    def __mul__(self, other):
        other = as_interval(other)
        products = [x * y for x in (self.lower, self.upper)
                    for y in (other.lower, other.upper)]
        return Interval(min(products), max(products))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lower <= 0 <= self.upper:
            raise ZeroDivisionError("interval contains zero")
        return Interval(1 / self.upper, 1 / self.lower)

    def __truediv__(self, other):
        return self * as_interval(other).reciprocal()

    def round_out(self, places=15):
        scale = 10 ** places
        lower = (self.lower * scale).__floor__()
        upper = (self.upper * scale).__ceil__()
        return Interval(F(lower, scale), F(upper, scale))


def as_interval(value):
    return value if isinstance(value, Interval) else Interval(F(value), F(value))


def log_rational(value: F, terms=96) -> Interval:
    if value <= 0:
        raise ValueError("logarithm argument must be positive")
    if value == 1:
        return Interval(F(0), F(0))
    if value < 1:
        return -log_rational(1 / value, terms)
    x = (value - 1) / (value + 1)
    xx = x * x
    power = x
    partial = F(0)
    for j in range(terms):
        partial += 2 * power / (2 * j + 1)
        power *= xx
    remainder = 2 * power / ((2 * terms + 1) * (1 - xx))
    return Interval(partial, partial + remainder)


def log_interval(value: Interval) -> Interval:
    return Interval(log_rational(value.lower).lower,
                    log_rational(value.upper).upper).round_out()


def decimal_exact(value: F, places=15) -> str:
    scaled = value * (10 ** places)
    if scaled.denominator != 1:
        raise ValueError("decimal endpoint is not on the requested grid")
    number = scaled.numerator
    sign = "-" if number < 0 else ""
    digits = str(abs(number)).zfill(places + 1)
    return sign + digits[:-places] + "." + digits[-places:]


def render(value):
    value = value.round_out()
    return {"lower": decimal_exact(value.lower),
            "upper": decimal_exact(value.upper),
            "endpoint_meaning": "exact decimal rationals"}


def verify():
    l2 = log_rational(F(2)).round_out()
    l3 = log_rational(F(3)).round_out()
    l5 = log_rational(F(5)).round_out()
    h = log_rational(F(3, 2)).round_out()
    alpha = h.reciprocal().round_out()
    p = (alpha * l2).round_out()
    kappa = (F(1, 2) - alpha + alpha * log_interval(2 * alpha)).round_out()
    moment5 = (alpha * l5 - 2).round_out()
    differences = {
        "alpha_above_three_halves": alpha - F(3, 2),
        "alpha_below_five_halves": F(5, 2) - alpha,
        "p_above_one": p - 1,
        "kappa_above_p": kappa - p,
        "kappa_below_2p_minus_one": 2 * p - 1 - kappa,
        "fifth_moment_exponent_above_p": moment5 - p,
        "kappa_above_fifth_moment_exponent": kappa - moment5,
        "large_b_comparison_exponent": F(3, 2) * (l3 - 1),
        "axis_upper_remainder_exponent": 2 * log_rational(F(5, 3)) - 1,
        "axis_test_negative_main_exponent": 1 - 2 * h,
        "middle_cutoff_deficit_gap": F(1, 2) - l2 / 2,
        "upper_cutoff_deficit_gap": l2 - (F(3, 2) * l3 - 1),
    }
    for label, value in differences.items():
        if value.lower <= 0:
            raise AssertionError((label, value))
    return {
        "status": "all exact rational inequalities verified",
        "method": "positive atanh series with a geometric rational tail",
        "series_terms": 96,
        "constants": {"alpha": render(alpha), "p": render(p),
                      "kappa": render(kappa),
                      "naive_fifth_moment_exponent": render(moment5)},
        "positive_differences": {name: render(value)
                                 for name, value in differences.items()},
        "scope": "Strict parameter inequalities only; analytic theorems are proved in the article.",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" /
                        "order_exponent_certificate.json")
    args = parser.parse_args()
    result = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])
    print(f"Checked {len(result['positive_differences'])} strict inequalities.")
    print(args.output)


if __name__ == "__main__":
    main()
