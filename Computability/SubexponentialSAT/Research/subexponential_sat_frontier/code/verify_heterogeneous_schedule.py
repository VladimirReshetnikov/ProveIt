"""Exact certificates for the heterogeneous-depth contraction schedule.

This does not implement the contraction algorithm. It verifies the arithmetic
of its proposed schedule and rigorously encloses its leading coefficient.
Python 3.10+, standard library only. No correctness gate relies on assert.
"""
from __future__ import annotations

from fractions import Fraction as F
from math import isqrt
from decimal import Decimal, localcontext
import json


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def sqrt_bounds(x: F, digits: int = 60) -> tuple[F, F]:
    require(x >= 0, "negative radical")
    scale = 10**digits
    q = isqrt(x.numerator * scale * scale // x.denominator)
    lo, hi = F(q, scale), F(q + 1, scale)
    require(lo * lo <= x <= hi * hi, "sqrt bracket failed")
    return lo, hi


def atan_bounds(x: F, terms: int = 100) -> tuple[F, F]:
    require(0 < x < 1, "atan requires 0<x<1")
    total = sum(((-1)**j * x**(2*j+1) / (2*j+1)
                 for j in range(terms)), F(0))
    next_total = total + (-1)**terms * x**(2*terms+1)/(2*terms+1)
    return min(total, next_total), max(total, next_total)


def constants() -> tuple[tuple[F, F], tuple[F, F]]:
    a, b = atan_bounds(F(1, 5)), atan_bounds(F(1, 239))
    pi = (16*a[0]-4*b[1], 16*a[1]-4*b[0])
    x, terms = F(1, 3), 100
    lo = 2*sum((x**(2*j+1)/(2*j+1) for j in range(terms)), F(0))
    rem = 2*x**(2*terms+1)/((2*terms+1)*(1-x*x))
    return pi, (lo, lo+rem)


ALPHABETS = (13, 14, 8, 6)
RANGES = (F(27, 2000), F(51, 4000), F(141, 20000), F(107, 20000))
TAIL_ALPHABET, TAIL_FIRST, TAIL_RATIO = 4, F(27, 6400), F(5, 8)


def decimal(x: F, precision: int = 55, rounding: str = 'ROUND_HALF_EVEN') -> str:
    with localcontext() as ctx:
        ctx.prec = precision
        ctx.rounding = rounding
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def coefficient_bounds() -> tuple[F, F]:
    lo = hi = F(0)
    prefix = F(1)
    for r, u in zip(ALPHABETS, RANGES):
        radical = sqrt_bounds(2*(1-F(1, r))/u)
        lo += prefix*radical[0]
        hi += prefix*radical[1]
        prefix *= F(2, r)
    require(prefix == F(1, 546), "wrong tail size prefix")
    radical = sqrt_bounds(2*(1-F(1, TAIL_ALPHABET))/TAIL_FIRST)
    decay = sqrt_bounds(F(2, 5))  # (2/4)/sqrt(5/8)
    lo += prefix*radical[0]/(1-decay[0])
    hi += prefix*radical[1]/(1-decay[1])
    pi, ln2 = constants()
    return pi[0]*lo/ln2[1], pi[1]*hi/ln2[0]


def finite_schedule(lam: int, depth: int) -> dict:
    require(lam >= 2 and depth >= 0, "invalid finite schedule request")
    # ceil(6 log2 lambda) is overapproximated by 6 ceil(log2 lambda).
    b = 6*(lam-1).bit_length()
    ranges = []
    for d in range(depth+1):
        q = RANGES[d] if d < 4 else TAIL_FIRST*TAIL_RATIO**(d-4)
        ranges.append((q*lam).numerator//(q*lam).denominator)
    return {"u": ranges, "a": sum(ranges)+(depth+1)*b, "buffer": b}


def main() -> dict:
    cumulative = []
    s = F(0)
    for q in RANGES:
        s += q
        cumulative.append(s)
    cap = s+TAIL_FIRST/(1-TAIL_RATIO)
    require(cumulative == [F(27,2000), F(21,800), F(333,10000), F(773,20000)],
            "cumulative capacities mismatch")
    require(cap == F(499,10000), "tail total capacity mismatch")
    # Root: 2 a_0 log2(13)<1/10. Later: a_d log2(r_d)<1/10.
    exact_power_checks = {
        "root_13^27_lt_2^100": 13**27 < 2**100,
        "depth1_14^21_lt_2^80": 14**21 < 2**80,
        "depth2_999_lt_1000": 999 < 1000,
        "depth3_6^773_lt_2^2000": 6**773 < 2**2000,
        "tail_998_lt_1000": 998 < 1000,
    }
    require(all(exact_power_checks.values()), "packing capacity failed")
    require(F(1,5)+cap < 1, "fresh-side or rounding capacity failed")
    require(cap < F(9,10), "new degree bound failed")
    require(F(3,5) < TAIL_RATIO < 1, "u must decay slower than crude child shrink")
    require(F(2,5) < 1, "tail work series does not converge")
    lo, hi = coefficient_bounds()
    require(F(6385220339054, 10**11) < lo < hi < F(6385220339056, 10**11),
            "coefficient outside the announced decimal bracket")
    # Exact finite checks exercise the integer schedule, not giant networks.
    finite = []
    for lam in (10**8, 10**12, 10**20):
        row = finite_schedule(lam, 12)
        require(all(u > 0 for u in row["u"]), "nonpositive sampled range")
        require(row["a"] <= cap*lam+13*row["buffer"], "integer cap failed")
        finite.append({"lambda": str(lam), "depth": 12,
                       "minimum_u": str(min(row["u"])),
                       "packet_exponent_a": str(row["a"]),
                       "additive_buffer": row["buffer"]})
    return {
        "status": "passed",
        "scope": "exact schedule arithmetic, not SAT performance or formal proof",
        "alphabets_prefix": list(ALPHABETS), "alphabet_tail": TAIL_ALPHABET,
        "range_fractions_prefix": [str(x) for x in RANGES],
        "range_tail_first": str(TAIL_FIRST), "range_tail_ratio": str(TAIL_RATIO),
        "cumulative_capacities": [str(x) for x in cumulative],
        "infinite_total_capacity": str(cap),
        "strict_power_certificates": exact_power_checks,
        "fresh_side_and_rounding_upper_power": str(F(1,5)+cap),
        "coefficient_lower": decimal(lo, rounding='ROUND_FLOOR'),
        "coefficient_upper": decimal(hi, rounding='ROUND_CEILING'),
        "finite_arithmetic_examples": finite,
    }


if __name__ == "__main__":
    print(json.dumps(main(), indent=2, sort_keys=True))
