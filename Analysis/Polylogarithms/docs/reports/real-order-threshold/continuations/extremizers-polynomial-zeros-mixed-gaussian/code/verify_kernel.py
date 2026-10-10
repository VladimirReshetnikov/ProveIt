#!/usr/bin/env python3
"""Replay exact rational enclosures for Section 2 (standard library only).

The stored decimal brackets are proposed rational endpoints, not floating-point
input to a proof.  This program recomputes their signs using Fraction arithmetic
and elementary Taylor remainder bounds, encloses the derived constants, and
checks finite polynomial identities at the N=2 algebraic solution.  Root
uniqueness and identification with the global extrema use the analytic proofs
in Section 2; this program does not formalize those proofs.

Run ``python code/verify_kernel.py`` from any working directory to verify the
shipped JSON.  Use ``--write`` to regenerate the deterministic certificate.
No mpmath, SymPy, NumPy, or plotting package is imported here.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from pathlib import Path
import time


BASE = Path(__file__).resolve().parents[1]
CERTIFICATE = BASE / "data" / "kernel_certificate.json"
LOG_TERMS = 96
EXP_TERMS = 48


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("Reversed interval")

    @staticmethod
    def point(x):
        x = F(x)
        return Interval(x, x)

    def __add__(self, other):
        other = as_interval(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-as_interval(other))

    def __rsub__(self, other):
        return as_interval(other) + (-self)

    def __mul__(self, other):
        other = as_interval(other)
        products = [a * b for a in (self.lo, self.hi)
                    for b in (other.lo, other.hi)]
        return Interval(min(products), max(products))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("Interval contains zero")
        return Interval(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other):
        return self * as_interval(other).reciprocal()

    def __rtruediv__(self, other):
        return as_interval(other) * self.reciprocal()

    def __pow__(self, power):
        if not isinstance(power, int) or power < 0:
            raise ValueError("Only nonnegative integer powers are supported")
        result = Interval.point(1)
        for _ in range(power):
            result *= self
        return result


def as_interval(x):
    return x if isinstance(x, Interval) else Interval.point(x)


def log_above_one(x: F) -> Interval:
    """Bound log(x), 1<=x<=2, by its positive atanh series.

    For u=(x-1)/(x+1), the omitted terms after j=0,...,m-1 are
    between zero and 2*u**(2*m+1)/((2*m+1)*(1-u*u)).
    """
    if not F(1) <= x <= F(2):
        raise ValueError("The reduced logarithm argument must lie in [1,2]")
    u = (x - 1) / (x + 1)
    u2 = u * u
    power = u
    total = F(0)
    for j in range(LOG_TERMS):
        total += 2 * power / (2 * j + 1)
        power *= u2
    tail = 2 * power / ((2 * LOG_TERMS + 1) * (1 - u2))
    return Interval(total, total + tail)


def exp_nonnegative(x: F) -> Interval:
    """Bound exp(x), 0<=x<=1, by a positive Taylor series.

    After degree m, the first omitted term is x**(m+1)/(m+1)!.
    The subsequent term ratios are at most x/(m+2), giving a
    geometric upper bound on the entire remainder.
    """
    if not F(0) <= x <= F(1):
        raise ValueError("The exponential argument must lie in [0,1]")
    term = F(1)
    total = term
    for j in range(1, EXP_TERMS + 1):
        term = term * x / j
        total += term
    first_omitted = term * x / (EXP_TERMS + 1)
    tail = first_omitted / (1 - x / (EXP_TERMS + 2))
    return Interval(total, total + tail)


def exp_negative_interval(x: Interval) -> Interval:
    """Bound exp(-x) on a nonnegative interval contained in [0,1]."""
    lower_exponential = exp_nonnegative(x.lo)
    upper_exponential = exp_nonnegative(x.hi)
    return Interval(1 / upper_exponential.hi, 1 / lower_exponential.lo)


def q_value(y: F, log2: Interval) -> Interval:
    if not F(1) <= 8 * y <= F(2):
        raise ValueError("Root bracket does not meet the logarithm reduction")
    logy = log_above_one(8 * y) - 3 * log2
    return 1 + y - y * y - y**3 + 4 * y * logy


G = [-4, 0, 59, 17, -10, -2, 3, 1]
D = [4, 36, 17, -6, -2, 2, 1]


def poly_value(coefficients, x):
    result = 0
    for coefficient in reversed(coefficients):
        result = result * x + coefficient
    return result


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def poly_add(p, q):
    answer = [0] * max(len(p), len(q))
    for i, coefficient in enumerate(p):
        answer[i] += coefficient
    for i, coefficient in enumerate(q):
        answer[i] += coefficient
    return trim(answer)


def poly_multiply(p, q):
    answer = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            answer[i + j] += a * b
    return trim(answer)


def poly_power(p, exponent):
    answer = [1]
    for _ in range(exponent):
        answer = poly_multiply(answer, p)
    return answer


def monic_remainder(p, modulus):
    if modulus[-1] != 1:
        raise ValueError("The modulus must be monic")
    answer = trim(p)
    while len(answer) >= len(modulus):
        offset = len(answer) - len(modulus)
        leading = answer[-1]
        for j, coefficient in enumerate(modulus):
            answer[offset + j] -= leading * coefficient
        answer = trim(answer)
    return answer


def substituted_gradient_remainder(terms, p_degree):
    """Return D**degree * P(12/D,y) modulo the monic polynomial G."""
    answer = [0]
    for p_power, y_power, coefficient in terms:
        term = [0] * y_power + [coefficient * 12**p_power]
        term = poly_multiply(term, poly_power(D, p_degree - p_power))
        answer = poly_add(answer, term)
    return monic_remainder(answer, G)


def exact_polynomial_checks():
    # The numerator polynomials of the two stationary equations in Section 2.
    p_terms = [(4, 4, -1), (3, 4, -2), (3, 2, -2), (2, 4, -1),
               (2, 2, -8), (2, 0, -1), (1, 2, -2), (1, 0, -2),
               (0, 0, 3)]
    q_terms = [(3, 4, -1), (2, 4, -1), (2, 2, -2), (1, 2, -6),
               (1, 1, -8), (1, 0, -1), (0, 0, 3)]
    if substituted_gradient_remainder(p_terms, 4) != [0]:
        raise ArithmeticError("The first stationary equation failed modulo G")
    if substituted_gradient_remainder(q_terms, 3) != [0]:
        raise ArithmeticError("The second stationary equation failed modulo G")

    # G'(y)/y - 68 = 7y^5+18y^4+51y+10(1-y^3)+40(1-y^2).
    derivative_over_y = [(j + 2) * G[j + 2] for j in range(len(G) - 2)]
    derivative_over_y[0] -= 68
    positivity_decomposition = [50, 51, -40, -10, 18, 7]
    if derivative_over_y != positivity_decomposition:
        raise ArithmeticError("The derivative positivity identity failed")
    if not (poly_value(G, F(0)) < 0 < poly_value(G, F(1))):
        raise ArithmeticError("The polynomial endpoint signs failed")
    if not 5**15 > 2**34:
        raise ArithmeticError("The exact B(1/4)>1 integer comparison failed")
    return {
        "D^4 P(12/D,y) modulo G": "zero",
        "D^3 Q_2(12/D,y) modulo G": "zero",
        "G_derivative_positive_decomposition":
            "G'(y)/y-68=7y^5+18y^4+51y+10(1-y^3)+40(1-y^2)",
        "G_at_0": -4,
        "G_at_1": 64,
        "B_at_one_quarter_exceeds_one": "5^15 > 2^34",
    }


def decimal_string(integer, digits):
    sign = "-" if integer < 0 else ""
    integer = abs(integer)
    whole, remainder = divmod(integer, 10**digits)
    return f"{sign}{whole}.{remainder:0{digits}d}"


def encode_interval(interval, digits=45):
    """Round outward to rational endpoints on the 10**(-digits) grid."""
    scale = 10**digits
    low = interval.lo.numerator * scale // interval.lo.denominator
    high = -((-interval.hi.numerator * scale) // interval.hi.denominator)
    lower = F(low, scale)
    upper = F(high, scale)
    if not lower <= interval.lo <= interval.hi <= upper:
        raise ArithmeticError("Outward rounding failed")
    return {
        "lower": str(lower),
        "upper": str(upper),
        "lower_decimal": decimal_string(low, digits),
        "upper_decimal": decimal_string(high, digits),
        "endpoint_convention": "inclusive; rounded outward using exact integers",
    }


def bracket(decimal_lower):
    digits = len(decimal_lower.split(".")[1])
    low = F(decimal_lower)
    return Interval(low, low + F(1, 10**digits))


def build_certificate():
    yinf = bracket("0.14530385925935842387355586312046141174251981604562")
    y2 = bracket("0.25270267836664057463358746330674822591370056250810")
    log2 = log_above_one(F(2))
    q_left = q_value(yinf.lo, log2)
    q_right = q_value(yinf.hi, log2)
    if not (q_left.lo > 0 and q_right.hi < 0):
        raise ArithmeticError("Exact logarithm bounds did not certify Q signs")

    g_left = poly_value(G, y2.lo)
    g_right = poly_value(G, y2.hi)
    if not (g_left < 0 < g_right):
        raise ArithmeticError("Exact rational G endpoint signs failed")

    cinf = (1 + yinf) / (2 * yinf)
    minf = (1 + yinf) * exp_negative_interval(yinf * (1 + yinf) / 2)
    mu1 = minf * cinf**2 * yinf**2 / 2
    d_interval = poly_value(D, y2)
    if not d_interval.lo > 0:
        raise ArithmeticError("D is not certified positive on the root bracket")
    p2 = 12 / d_interval
    m2 = p2 * (1 + y2) * (4 / ((1 + p2) * (1 + p2 * y2**2)) - 1)
    if not (0 < p2.lo <= p2.hi < 1 and minf.lo > 1 and m2.lo > minf.hi):
        raise ArithmeticError("A physical-domain or strict-value check failed")

    return {
        "schema_version": 1,
        "arithmetic": "Python standard-library fractions.Fraction and integers",
        "scope": (
            "Exact endpoint-sign and value-enclosure certificates. The unique "
            "root and global-extremum identifications use Section 2's analytic "
            "proofs. General finite-N optimization is not certified by this file."
        ),
        "analytic_inputs": [
            "Q has a unique root in (0,1), the limiting global extremizer.",
            "M_inf=(1+y_inf)*exp(-y_inf*(1+y_inf)/2).",
            "The N=2 global maximum is the unique interior stationary point.",
            "G's unique root in (0,1) gives p2=12/D(y2).",
        ],
        "series_bounds": {
            "logarithm_terms": LOG_TERMS,
            "logarithm_reduction": "log(y)=log(8y)-3*log(2)",
            "logarithm_tail":
                "0 <= tail <= 2*u^(2*m+1)/((2*m+1)*(1-u^2))",
            "exponential_degree": EXP_TERMS,
            "exponential_tail":
                "0 <= tail <= x^(m+1)/(m+1)!/(1-x/(m+2)) for 0<=x<=1",
            "negative_exponential": "exp(-x)=1/exp(x), with interval inversion",
        },
        "input_root_brackets": {
            "y_inf": {"lower": str(yinf.lo), "upper": str(yinf.hi)},
            "y2": {"lower": str(y2.lo), "upper": str(y2.hi)},
        },
        "endpoint_signs": {
            "Q_at_y_inf_lower": encode_interval(q_left, 75),
            "Q_at_y_inf_upper": encode_interval(q_right, 75),
            "G_at_y2_lower": encode_interval(Interval.point(g_left), 75),
            "G_at_y2_upper": encode_interval(Interval.point(g_right), 75),
        },
        "certified_intervals": {
            "y_inf": encode_interval(yinf),
            "c_inf": encode_interval(cinf),
            "M_inf": encode_interval(minf),
            "mu1": encode_interval(mu1),
            "y2": encode_interval(y2),
            "p2": encode_interval(p2),
            "M2": encode_interval(m2),
        },
        "exact_polynomial_checks": exact_polynomial_checks(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true",
                        help="Regenerate the JSON instead of comparing it")
    args = parser.parse_args()
    start = time.perf_counter()
    certificate = build_certificate()
    if args.write:
        CERTIFICATE.parent.mkdir(parents=True, exist_ok=True)
        CERTIFICATE.write_text(json.dumps(certificate, indent=2) + "\n")
        action = "Wrote"
    else:
        if not CERTIFICATE.exists():
            raise FileNotFoundError("Run with --write to create the certificate")
        stored = json.loads(CERTIFICATE.read_text())
        if stored != certificate:
            raise ArithmeticError("Stored kernel certificate differs from replay")
        action = "Verified"
    print(f"{action} {CERTIFICATE.name} using exact rational arithmetic.")
    for name, enclosure in certificate["certified_intervals"].items():
        print(f"{enclosure['lower_decimal']} <= {name} "
              f"<= {enclosure['upper_decimal']}")
    print(f"Elapsed: {time.perf_counter() - start:.3f} seconds")


if __name__ == "__main__":
    main()
