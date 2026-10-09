#!/usr/bin/env python3
"""Exact rational enclosures for the Herglotz--Zagier function.

All interval endpoints are fractions.  The Euler--Maclaurin coefficients
are enclosed using the positive coth partial-fraction kernel proved in
the article, not a floating-point error estimate.  The same article proves
the first-omitted-term bound and the two moment bounds used here.
Only the Python standard library is needed to generate the certificates.
"""

from dataclasses import dataclass
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
from pathlib import Path
import argparse
import json
import sys


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("Reversed interval")

    @staticmethod
    def point(x):
        return Interval(Q(x), Q(x))

    def __add__(self, other):
        other = other if isinstance(other, Interval) else Interval.point(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, Interval) else -Q(other))

    def __mul__(self, other):
        other = other if isinstance(other, Interval) else Interval.point(other)
        candidates = [a * b for a in (self.lo, self.hi)
                      for b in (other.lo, other.hi)]
        return Interval(min(candidates), max(candidates))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = other if isinstance(other, Interval) else Interval.point(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("Interval includes zero")
        return self * Interval(1 / other.hi, 1 / other.lo)

    def square(self):
        if self.lo < 0 < self.hi:
            return Interval(Q(0), max(self.lo**2, self.hi**2))
        return Interval(min(self.lo**2, self.hi**2),
                        max(self.lo**2, self.hi**2))


@lru_cache(maxsize=None)
def bernoulli_numbers(limit):
    """Akiyama--Tanigawa recurrence; the convention for B_1 is irrelevant."""
    a, numbers = [], []
    for m in range(limit + 1):
        a.append(Q(1, m + 1))
        for j in range(m, 0, -1):
            a[j - 1] = j * (a[j - 1] - a[j])
        numbers.append(a[0])
    return tuple(numbers)


@lru_cache(maxsize=None)
def zeta_interval(s, cutoff=48, order=48):
    """Euler--Maclaurin coefficients with a proved positive-kernel bound."""
    if s < 2 or cutoff < 2 or order < 1:
        raise ValueError("Require s>=2, cutoff>=2, order>=1")
    b = bernoulli_numbers(2 * order)
    value = sum((Q(1, n**s) for n in range(1, cutoff)), Q(0))
    value += Q(1, (s - 1) * cutoff**(s - 1))
    value += Q(1, 2 * cutoff**s)
    rising = 1
    for j in range(1, 2 * order):
        rising *= s + j - 1
        if j % 2 == 1:
            k = (j + 1) // 2
            term = b[2 * k] * Q(rising,
                                      factorial(2 * k) * cutoff**(s + j))
            if k < order:
                value += term
            else:
                # Expand 2t sum_n 1/(t^2+(2pi n)^2) geometrically.
                # Its exact remainder is bounded by this first omitted
                # Bernoulli term after positive Laplace integration.
                remainder = abs(term)
    return Interval(value - remainder, value + remainder)


def moment_interval(k, cutoff=48, order=48, bernoulli_limit=128):
    # mu_k = |B_(2k+2)| zeta(2k+3)/(2k+2); no pi evaluation is needed.
    b = bernoulli_numbers(max(bernoulli_limit, 2 * k + 2))
    return zeta_interval(2 * k + 3, cutoff, order) * (abs(b[2*k+2]) / (2*k+2))


def enclose(x, terms, cutoff=48, order=48):
    """Certified interval for F(x), x a positive rational, terms>=0."""
    x = Q(x)
    if x <= 0 or terms < 0:
        raise ValueError("Require x>0 and terms>=0")
    y = x*x
    mu = [moment_interval(k, cutoff, order,
                          max(128, 2*terms+6)) for k in range(terms+3)]
    if any(m.lo <= 0 for m in mu):
        raise ValueError("Increase cutoff/order to certify positive moments")
    partial = Interval.point(0)
    for k in range(terms):
        partial += mu[k] * ((-1)**k / y**(k+1))
    omitted = mu[terms] / y**(terms+1)
    lower = mu[terms].square() / (y*mu[terms] + mu[terms+1]) / y**terms
    next_lower = (mu[terms+1].square()
                  / (y*mu[terms+1] + mu[terms+2]) / y**(terms+1))
    upper = omitted - next_lower
    remainder = Interval(max(Q(0), lower.lo), upper.hi)
    approximation = -zeta_interval(2, cutoff, order) / (2*x) - partial
    result = approximation + remainder * ((-1)**(terms+1))
    return result, remainder, omitted


def fraction_record(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def decimal_endpoint(x, places, rounding):
    with localcontext() as ctx:
        ctx.prec = places
        ctx.rounding = rounding
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def interval_record(interval, digits=65):
    return {"lower": fraction_record(interval.lo),
            "upper": fraction_record(interval.hi),
            "decimal_lower": decimal_endpoint(interval.lo, digits, ROUND_FLOOR),
            "decimal_upper": decimal_endpoint(interval.hi, digits, ROUND_CEILING),
            "width_upper": decimal_endpoint(interval.hi-interval.lo, 12, ROUND_CEILING)}


def main():
    # Certificates produced here contain controlled exact integers larger
    # than Python's default decimal serialization limit.
    sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data"/"rational_intervals.json")
    args = parser.parse_args()
    # These choices are concrete examples, not a floating-point optimization
    # gate.  The enclosing theorem is valid for every nonnegative term count.
    cases = [(Q(2), 6), (Q(4), 12), (Q(8), 25), (Q(16), 50)]
    records = []
    for x, terms in cases:
        result, remainder, omitted = enclose(x, terms)
        assert 0 < remainder.lo <= remainder.hi < omitted.hi
        records.append({"x": str(x), "terms": terms,
                        "F_interval": interval_record(result),
                        "remainder_interval": interval_record(remainder),
                        "first_omitted_term": interval_record(omitted)})
        print(f"x={x}, N={terms}, certified width <= "
              f"{records[-1]['F_interval']['width_upper']}", flush=True)
    payload = {"arithmetic": "exact rational, Python fractions.Fraction",
               "zeta_cutoff": 48, "zeta_EM_order": 48,
               "rounding": "decimal_lower downward; decimal_upper upward",
               "cases": records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {args.output.name}")


if __name__ == "__main__":
    main()
