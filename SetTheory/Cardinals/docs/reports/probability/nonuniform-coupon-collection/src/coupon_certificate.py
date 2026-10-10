"""Certified fixed-time probabilities for nonuniform coupon collection.

The accompanying article proves the analytic error bound. All numerical
operations in this implementation use Arb real balls (python-flint), so the
returned enclosure includes both the analytic remainder and rounding error.
Inputs are nonnegative rational weights; they are normalized exactly.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
from typing import Iterable

from flint import arb, ctx, fmpq


def as_fraction(value) -> Fraction:
    """Interpret strings as exact rationals/decimals, and reject float input."""
    if isinstance(value, float):
        raise TypeError("Use a decimal string or Fraction, not a binary float.")
    return Fraction(value)


def ball(value) -> arb:
    if isinstance(value, Fraction):
        return arb(fmpq(value.numerator, value.denominator))
    return arb(value)


def choose(m: int, j: int) -> int:
    return comb(m, j) if 0 <= j <= m else 0


@lru_cache(maxsize=128)
def charlier_coefficients(m: int, degree: int) -> tuple[Fraction, ...]:
    """Coefficients of (1-x)^m exp(m*x), through the requested degree."""
    if m < 0 or degree < 0:
        raise ValueError("m and degree must be nonnegative integers.")
    coefficients = [Fraction(1)]
    prefix = Fraction(0)
    for k in range(1, degree + 1):
        if k >= 2:
            prefix += coefficients[k - 2]
        coefficients.append(-m * prefix / k)
    return tuple(coefficients)


def poly_mul(left, right, degree):
    """Truncated ordinary power-series product, valid for rationals or balls."""
    zero = left[0] * 0
    result = [zero for _ in range(degree + 1)]
    for k in range(degree + 1):
        start = max(0, k - len(right) + 1)
        stop = min(k, len(left) - 1)
        result[k] = sum(
            (left[j] * right[k - j] for j in range(start, stop + 1)), zero
        )
    return result


def poly_power(base, exponent, degree):
    zero = base[0] * 0
    result = [zero + 1] + [zero for _ in range(degree)]
    while exponent:
        if exponent & 1:
            result = poly_mul(result, base, degree)
        exponent >>= 1
        if exponent:
            base = poly_mul(base, base, degree)
    return result


@lru_cache(maxsize=32)
def coefficient_tails(order: int) -> tuple[Fraction, ...]:
    """theta[j] = 1 - sum_{k<2s} [x^k] d(x)^j; theta[0] is unused."""
    if order < 1:
        raise ValueError("The order must be a positive integer.")
    degree = 2 * order - 1
    d = [Fraction(0), Fraction(0)]
    d += [Fraction(k - 1, factorial(k)) for k in range(2, degree + 1)]
    d = d[: degree + 1]
    power = [Fraction(1)] + [Fraction(0)] * degree
    tails = [Fraction(0)]
    for j in range(1, order):
        power = poly_mul(power, d, degree)
        tail = 1 - sum(power)
        if not 0 <= tail <= 1:
            raise ArithmeticError("An exact coefficient-tail invariant failed.")
        tails.append(tail)
    return tuple(tails)


@dataclass
class Certificate:
    n: int
    m: int
    order: int
    bits: int
    approximation: arb
    analytic_radius: arb
    enclosure: arb
    poisson: arb
    poisson_missing_mean: arb
    coarse_radius: arb
    prior_majorant: arb
    moments: tuple[arb, ...]

    def as_dict(self, digits=25):
        """Ball strings retain outward error bounds; floats are not certificates."""
        result = {name: getattr(self, name) for name in ("n", "m", "order", "bits")}
        for name in (
            "approximation", "analytic_radius", "enclosure", "poisson",
            "poisson_missing_mean", "coarse_radius", "prior_majorant",
        ):
            result[name] = getattr(self, name).str(digits)
        result["interpretation"] = "The true probability is in enclosure intersect [0,1]."
        result["comparison"] = "prior_majorant = 33*m^order*M_(2*order); not the full prior seminorm"
        return result


def coverage_certificate(
    weights: Iterable, m: int, order: int = 2, bits: int = 160,
    group_equal: bool = True,
) -> Certificate:
    """Compute the proved probability enclosure from exact rational weights.

    The product work is O(n*order^2), with O(order^3) cached rational setup.
    Equal weights may be grouped and their series factors exponentiated.
    This is an arithmetic-operation bound, not a unit-cost bit-complexity claim.
    """
    if not isinstance(m, int) or m < 1:
        raise ValueError("m must be a positive integer.")
    if not isinstance(order, int) or order < 1:
        raise ValueError("order must be a positive integer.")
    if bits < 64:
        raise ValueError("Use at least 64 bits of working precision.")
    weights = [as_fraction(w) for w in weights]
    if not weights or min(weights) < 0 or sum(weights) == 0:
        raise ValueError("Use a nonempty vector of nonnegative weights with positive sum.")
    total = sum(weights)
    n = len(weights)
    grouped = Counter(weights).items() if group_equal else ((w, 1) for w in weights)
    f_degree, z_degree = 2 * order - 1, 3 * order

    with ctx.workprec(bits):
        f_jet = [arb(1)] + [arb(0) for _ in range(f_degree)]
        z_jet = [arb(1)] + [arb(0) for _ in range(z_degree)]
        missing_mean = arb(0)
        for weight, multiplicity in grouped:
            u = ball(m * weight / total)
            q = (-u).exp()
            missing_mean += multiplicity * q
            terms = [q]
            for k in range(1, z_degree + 1):
                terms.append(terms[-1] * u / k)
            f_factor = [1 - q] + [-x for x in terms[1:f_degree + 1]]
            z_factor = [1 + q] + terms[1:]
            if multiplicity > 1:
                f_factor = poly_power(f_factor, multiplicity, f_degree)
                z_factor = poly_power(z_factor, multiplicity, z_degree)
            f_jet = poly_mul(f_jet, f_factor, f_degree)
            z_jet = poly_mul(z_jet, z_factor, z_degree)

        # F(m-mz) and Z(m-mz) were differentiated in the dimensionless z.
        c = charlier_coefficients(m, f_degree)
        approximation = sum(
            (ball(c[k] * factorial(k) / m**k) * f_jet[k]
             for k in range(f_degree + 1)), arb(0)
        )
        moments = tuple(
            ball(Fraction(factorial(k), m**k)) * z_jet[k]
            for k in range(z_degree + 1)
        )
        theta = coefficient_tails(order)
        b = sum((choose(m, j) * theta[j] for j in range(1, order)), Fraction(0))
        k = 2 * order
        top = ball(Fraction(choose(m, order), 2**order))
        analytic_radius = ball(b) * moments[k] + top * sum(
            (choose(order, ell) * moments[k + ell] for ell in range(order + 1)),
            arb(0),
        )
        coarse_radius = ball(b + choose(m, order)) * moments[k]
        prior_majorant = 33 * m**order * moments[k]
        enclosure = approximation + arb(0, analytic_radius.upper())
        return Certificate(
            n, m, order, bits, approximation, analytic_radius, enclosure,
            f_jet[0], missing_mean, coarse_radius, prior_majorant, moments,
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--uniform", type=int, metavar="N")
    source.add_argument("--weights", help="Comma-separated rational weights, e.g. 1,2,3/2")
    source.add_argument("--weights-json", type=Path, help="JSON list of integers or rational strings")
    parser.add_argument("--m", type=int, required=True, help="Number of independent draws")
    parser.add_argument("--order", type=int, default=2)
    parser.add_argument("--bits", type=int, default=160)
    parser.add_argument("--ungrouped", action="store_true")
    args = parser.parse_args()
    if args.uniform is not None:
        weights = [1] * args.uniform
    elif args.weights is not None:
        weights = args.weights.split(",")
    else:
        weights = json.loads(args.weights_json.read_text())
    result = coverage_certificate(weights, args.m, args.order, args.bits, not args.ungrouped)
    print(json.dumps(result.as_dict(), indent=2))


if __name__ == "__main__":
    main()
