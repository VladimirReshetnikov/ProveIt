"""Rational brackets for delta = pi/2 - the upper-semicircle zero.

mpmath proposes a bracket.  The actual sign tests use Fraction arithmetic,
Taylor's theorem, and an explicit rational tail bound.  No floating point
number participates in acceptance of a bracket.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import argparse
import json
from package_io import read_json, write_json_new_or_compare


def harmonic_coefficients(a, b, terms):
    h = Q(0)
    result = []
    for n in range(1, terms + 1):
        result.append(h * Q(2, n)**a)
        h += Q(1, n**b)
    return result


def trig_interval(x, cosine, degree):
    """Taylor polynomial through even degree or odd degree-1, remainder."""
    total = Q(0)
    start = 0 if cosine else 1
    for j in range(start, degree + 1, 2):
        total += Q((-1)**((j - start)//2), factorial(j)) * x**j
    next_j = degree + 2 if cosine else degree + 1
    error = abs(x)**next_j / factorial(next_j)
    return total - error, total + error


def equation_interval(delta, coefficients, a, terms, degree):
    low = high = Q(0)
    for n, coefficient in enumerate(coefficients, 1):
        if not coefficient:
            continue
        lower, upper = trig_interval(n * delta, n % 2 == 1, degree)
        sign = (1 if n % 4 == 1 else -1) if n % 2 else (1 if n % 4 == 2 else -1)
        if sign < 0:
            lower, upper = -upper, -lower
        low += coefficient * lower
        high += coefficient * upper
    h_terms = sum((Q(1, k) for k in range(1, terms + 1)), Q(0))
    tail = Q(2**a, terms**(a - 1)) * (h_terms / (a - 1) + Q(1, (a - 1)**2))
    return low - tail, high + tail, tail


def certified_bracket(a, b, terms, digits, degree=60):
    import mpmath as mp
    coefficients = harmonic_coefficients(a, b, terms)
    mp.mp.dps = digits + 45
    floats = [mp.mpf(c.numerator) / c.denominator for c in coefficients]
    def equation(d):
        return mp.fsum(c * (mp.cos(n*d) if n % 2 else mp.sin(n*d))
                       * ((1 if n % 4 == 1 else -1) if n % 2
                          else (1 if n % 4 == 2 else -1))
                       for n, c in enumerate(floats, 1) if c)
    seed = (1 + mp.mpf(2)**(-b)) * (mp.mpf(2)/3)**a / 2
    approximate = mp.findroot(equation, (seed * mp.mpf('.8'), seed * mp.mpf('1.2')))
    denominator = 10**digits
    center = int(mp.floor(approximate * denominator))
    radius = 2
    while radius <= 64:
        lower = Q(center - radius, denominator)
        upper = Q(center + radius + 1, denominator)
        sign_lo = equation_interval(lower, coefficients, a, terms, degree)
        sign_hi = equation_interval(upper, coefficients, a, terms, degree)
        if sign_lo[1] < 0 < sign_hi[0]:
            return {"a": a, "b": b, "terms": terms, "taylor_degree": degree,
                    "delta_lower": str(lower), "delta_upper": str(upper),
                    "delta_lower_decimal": str(mp.mpf(lower.numerator)/lower.denominator),
                    "delta_upper_decimal": str(mp.mpf(upper.numerator)/upper.denominator),
                    "fourier_tail_bound": str(sign_lo[2]),
                    "left_sign": -1, "right_sign": 1,
                    "acceptance": "exact Fraction signs with rigorous Taylor and Fourier tails"}
        radius *= 2
    raise ArithmeticError("Could not certify bracket: increase Fourier terms or Taylor degree")


def verify_reference():
    """Replay saved rational brackets using no floating-point package."""
    reference = read_json("zero_brackets.json")
    results = []
    for item in reference["certified_brackets"]:
        a, b = item["a"], item["b"]
        terms, degree = item["terms"], item["taylor_degree"]
        assert all(isinstance(value, int) for value in (a, b, terms, degree))
        assert a >= 2 and b >= 1 and terms >= 2 and degree >= 2 and degree % 2 == 0
        lower, upper = Q(item["delta_lower"]), Q(item["delta_upper"])
        assert Q(0) < lower < upper < Q(1)
        coefficients = harmonic_coefficients(a, b, terms)
        left = equation_interval(lower, coefficients, a, terms, degree)
        right = equation_interval(upper, coefficients, a, terms, degree)
        assert left[1] < 0 < right[0], "Rational endpoint sign test failed"
        assert left[2] == right[2] == Q(item["fourier_tail_bound"])
        assert item["left_sign"] == -1 and item["right_sign"] == 1
        result = {"a": a, "b": b, "terms": terms, "taylor_degree": degree,
                  "delta_lower": str(lower), "delta_upper": str(upper),
                  "left_upper_strictly_negative": True,
                  "right_lower_strictly_positive": True,
                  "stored_fourier_tail_matched": True}
        results.append(result)
        print(f"PASS rational zero bracket: a={a}, b={b}, width={upper-lower}", flush=True)
    return {"arithmetic": "Python fractions.Fraction only", "certified_brackets": results,
            "scope": "exact endpoint signs and tails; uniqueness is proved in the article"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    cases = [(8, 1, 128, 10), (12, 1, 80, 16), (20, 1, 48, 24),
             (40, 1, 32, 43), (12, 2, 80, 16), (20, 4, 48, 24)]
    if args.quick:
        cases = cases[:2]
    results = []
    for a, b, terms, digits in cases:
        result = certified_bracket(a, b, terms, digits)
        results.append(result)
        print(a, b, result["delta_lower_decimal"], result["delta_upper_decimal"], flush=True)
    write_json_new_or_compare(args.output, {"certified_brackets": results})


if __name__ == "__main__":
    main()
