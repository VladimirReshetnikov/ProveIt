"""Finite exact checks of definitions and proof identities.

These are reproducibility checks, not a proof of the universal PNT.
Run from any directory: python3 /path/to/code/check_arithmetic.py
"""

from collections import defaultdict
from fractions import Fraction
from math import isqrt
import json

from arithmetic import (prime_count, denominator, logarithm_numerator,
                        logarithm_lower, pnt_matrix, contraction_parameters,
                        threshold_step, modulus_description)


def factors(n):
    out = {}
    for p in range(2, n + 1):
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
    return out


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def mu(n):
    f = factors(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def lam_symbol(n):
    f = factors(n)
    return {next(iter(f)): 1} if len(f) == 1 else {}


def product(v, w):
    out = defaultdict(int)
    for p, a in v.items():
        for q, b in w.items():
            out[tuple(sorted((p, q)))] += a * b
    return dict(out)


def add_scaled(out, term, scale=1):
    for monomial, coefficient in term.items():
        out[monomial] += scale * coefficient


def clean(poly):
    return {key: value for key, value in poly.items() if value}


def harmonic(n):
    return sum((Fraction(1, j) for j in range(1, n + 1)), Fraction())


def log_interval(a, b, m):
    lower = harmonic(m * a) - harmonic(m * b)
    return lower, lower + Fraction(1, m * b) - Fraction(1, m * a)


def main():
    checks = {}
    for n in range(1, 257):
        ds = divisors(n)
        assert sum(mu(d) for d in ds) == int(n == 1)
        linear = defaultdict(int)
        for d in ds:
            add_scaled(linear, lam_symbol(d))
        assert clean(linear) == factors(n)
        lhs = defaultdict(int)
        rhs = defaultdict(int)
        for d in ds:
            add_scaled(lhs, product(factors(n // d), factors(n // d)), mu(d))
            add_scaled(rhs, product(lam_symbol(d), lam_symbol(n // d)))
        add_scaled(rhs, product(lam_symbol(n), factors(n)))
        assert clean(lhs) == clean(rhs)
        m = isqrt(n)
        assert sum(len(divisors(j)) for j in range(1, n + 1)) == (
            2 * sum(n // d for d in range(1, m + 1)) - m * m)
    checks["symbolic_divisor_and_Selberg_identities"] = {"through_n": 256, "passed": True}

    count = 0
    for a in range(1, 9):
        for b in range(1, a + 1):
            for m in range(1, 4):
                for n in range(1, 4):
                    lo, hi = log_interval(a, b, m)
                    lof, hif = log_interval(a, b, m * n)
                    assert lo <= lof <= hif <= hi
                    assert hi - lo <= Fraction(1, m)
                    count += 1
    checks["rational_log_refinement"] = {"instances": count, "passed": True}

    for n in range(1, 41):
        d = denominator(n)
        a = logarithm_numerator(n)
        assert Fraction(a, d) == logarithm_lower(n)
        for j in range(n + 1, n * n + 1):
            assert d % j == 0
        for k in range(1, 9):
            exact = k * abs(Fraction(prime_count(n) * a, d) - n) <= n
            assert pnt_matrix(k, n) == exact
    checks["integer_matrix_and_denominators"] = {"through_n": 40, "through_k": 8, "passed": True}

    for q in range(1, 101):
        p = contraction_parameters(q)
        d, h, j, s = p["D"], p["H"], p["J"], p["Cs"]
        assert Fraction(4) - Fraction(j, d) == Fraction(1, q)
        assert Fraction(1, 4 * h * 64 * q * q) == Fraction(4, d)
        f = (1 << 20) * d
        assert 16 + 16 * d < f
        assert 16 * h + s * d + 2 < f
        assert d.bit_length() <= d // 16
        assert f.bit_length() <= d // 8
        for t in [2, 3, 17, 1000]:
            assert threshold_step(t, q) + 1 <= f * (t + 1)
    checks["contraction_constant_bookkeeping"] = {"through_q": 100, "passed": True}
    assert Fraction(1, 8) + Fraction(400, 4096) == Fraction(57, 256) < Fraction(1, 4)
    checks["prime_counting_error_budget"] = {"passed": True}
    return {"status": "all finite checks passed", "scope": "Not a universal PNT proof",
            "checks": checks, "symbolic_modulus_example": modulus_description(1)}


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
