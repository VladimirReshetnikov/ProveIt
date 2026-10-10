#!/usr/bin/env python3
"""Reproduce exact group-algebra checks and independent J quadrature checks.

The group checks use integers/Fractions only. Numerical checks are a
regression aid for the written proofs, not a certificate of period
independence and not a substitute for those proofs.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import mpmath as mp


def sign_class(a: int, q: int) -> int:
    a %= q
    return min(a, (-a) % q)


def group(q: int) -> list[int]:
    return sorted({sign_class(a, q) for a in range(1, q) if math.gcd(a, q) == 1})


def inverse(a: int, q: int) -> int:
    return sign_class(pow(a, -1, q), q)


def clean(v):
    return {a: c for a, c in v.items() if c}


def beta_vector(a: int, q: int) -> dict[int, int]:
    if q <= 2:
        return {}
    v = defaultdict(int)
    v[sign_class(a, q)] += 1
    v[inverse(a, q)] -= 1
    return clean(v)


def linear_combination(terms) -> dict[int, int]:
    v = defaultdict(int)
    for coefficient, w in terms:
        for a, c in w.items():
            v[a] += coefficient * c
    return clean(v)


def d_vector(a: int, q: int) -> dict[int, int]:
    return linear_combination([
        (1, beta_vector(a, q)),
        (-1, beta_vector(a * pow(2, -1, q), q)),
    ])


def t_vector(a: int, q: int) -> dict[int, int]:
    return linear_combination([
        (1, beta_vector(2 * a, q)),
        (-2, beta_vector(a, q)),
        (1, beta_vector(a * pow(2, -1, q), q)),
    ])


def exact_rank(rows: list[list[int]]) -> int:
    if not rows:
        return 0
    basis = {}
    for row in rows:
        v = [Fraction(c) for c in row]
        for pivot, b in sorted(basis.items()):
            if v[pivot]:
                coefficient = v[pivot]
                v = [a - coefficient * c for a, c in zip(v, b)]
        for pivot, coefficient in enumerate(v):
            if coefficient:
                basis[pivot] = [a / coefficient for a in v]
                break
    return len(basis)


def cosets_of_two(q: int):
    elements = group(q)
    h = set()
    a = 1
    while a not in h:
        h.add(a)
        a = sign_class(2 * a, q)
    unseen = set(elements)
    cosets = []
    while unseen:
        a = min(unseen)
        coset = {sign_class(a * b, q) for b in h}
        cosets.append(coset)
        unseen -= coset
    return h, cosets


def rank_formula(q: int) -> int:
    elements = group(q)
    h, cosets = cosets_of_two(q)
    involutions = sum(inverse(a, q) == a for a in elements)
    quotient_involutions = sum(sign_class(min(c) ** 2, q) in h for c in cosets)
    return (len(elements) - involutions - len(cosets) + quotient_involutions) // 2


def classification(p: int, q: int) -> str:
    fraction = Fraction(p, q)
    p, q = fraction.numerator, fraction.denominator
    if p % 2 and q % 2:
        if p == q == 1:
            return "logarithmic"
        if p in {1, 3, 5} and q in {1, 3, 5}:
            return "rational_dilogarithms_only"
        return "formal_obstruction"
    e, o = (p, q) if p % 2 == 0 else (q, p)
    first = o == 1 or e * e % o in {1 % o, (-1) % o}
    second = o * o % (2 * e) == 1
    return "logarithmic" if first and second else "formal_obstruction"


def group_checks(limit: int, rank_limit: int) -> dict:
    zero_tests = 0
    ranks = []
    for q in range(3, limit + 1, 2):
        elements = group(q)
        for a in elements:
            assert (not d_vector(a, q)) == (q in {3, 5}), ("D", q, a)
            square_is_sign = a * a % q in {1, q - 1}
            assert (not t_vector(a, q)) == square_is_sign, ("T", q, a)
            zero_tests += 2
        if q <= rank_limit:
            d_rows = [[d_vector(a, q).get(b, 0) for b in elements] for a in elements]
            t_rows = [[t_vector(a, q).get(b, 0) for b in elements] for a in elements]
            expected = rank_formula(q)
            assert exact_rank(d_rows) == expected
            assert exact_rank(t_rows) == expected
            assert exact_rank(d_rows + t_rows) == expected
            ranks.append({"q": q, "rho": expected, "group_size": len(elements)})
    # The manuscript's complete J(2/q) statement, compared after reduction.
    for q in range(2, limit + 1):
        actual = classification(2, q)
        expected_log = q in {2, 3, 5} or q % 4 == 0
        expected_rational = q in {2, 3, 5, 6, 10} or q % 4 == 0
        assert (actual == "logarithmic") == expected_log
        assert (actual != "formal_obstruction") == expected_rational
    for n in range(1, limit + 1):
        assert classification(n, n + 1) == "logarithmic"
    for e in range(2, limit + 1, 2):
        assert classification(e, e * e - 1) == "logarithmic"
        assert classification(e, e * e + 1) == "logarithmic"
    assert classification(3, 8) == "formal_obstruction"
    assert classification(3, 10) == "formal_obstruction"
    return {"odd_conductor_zero_tests": zero_tests, "limit": limit, "ranks": ranks}


def j_integral(p: int, q: int):
    # t=s^q makes the integrand analytic at s=0, eliminating endpoint
    # fractional-power regularity as a source of quadrature ambiguity.
    return mp.quad(lambda s: q * s ** (q - 1) * mp.log1p(s ** p) / (1 + s ** q), [0, 1])


def s_value(n: int):
    return mp.fsum(mp.log(2 * mp.sin(mp.pi * k / n)) ** 2 for k in range(1, n))


def consecutive_formula(n: int):
    return (
        mp.log(2) ** 2 / 2
        - mp.mpf(n * n - n - 1) * mp.pi ** 2 / (24 * n * (n + 1))
        + (s_value(n) - s_value(n + 1) - s_value(2 * n) + s_value(2 * n + 2)) / 2
    )


def numeric_checks(dps: int) -> dict:
    mp.mp.dps = dps
    phi = (1 + mp.sqrt(5)) / 2
    epsilon = 1 + mp.sqrt(2)
    li2 = lambda a, b: mp.polylog(2, mp.mpf(a) / b)
    log2, log3, log5 = map(mp.log, (2, 3, 5))
    exact_values = {
        (3, 4): -5 * mp.pi ** 2 / 288 + log2 ** 2 / 8 + mp.log(epsilon) ** 2 / 2,
        (4, 5): -11 * mp.pi ** 2 / 480 + 7 * log2 ** 2 / 8
                + 2 * mp.log(phi) ** 2 - mp.log(epsilon) ** 2 / 2,
        (3, 5): li2(1, 3) - li2(1, 5) / 2 - 7 * mp.pi ** 2 / 180
                + log2 ** 2 / 2 + log3 ** 2 / 2 - log5 ** 2 / 4 + mp.log(phi) ** 2,
        (3, 1): -mp.pi ** 2 / 9 + log2 ** 2 / 2 + log3 ** 2 / 2 + li2(1, 3),
        (5, 1): -7 * mp.pi ** 2 / 60 + log2 ** 2 / 2 + log5 ** 2 / 4
                + mp.log(phi) ** 2 + li2(1, 5) / 2,
    }
    checks = []
    tolerance = mp.mpf(10) ** (-(dps - 15))
    for (p, q), rhs in exact_values.items():
        lhs = j_integral(p, q)
        residual = abs(lhs - rhs)
        assert residual < tolerance, (p, q, residual)
        checks.append({"identity": f"J({p}/{q})", "residual": mp.nstr(residual, 12),
                       "value": mp.nstr(lhs, 60)})
    for n in [1, 2, 3, 4, 5, 7, 10, 16, 25, 40]:
        residual = abs(j_integral(n, n + 1) - consecutive_formula(n))
        assert residual < tolerance, ("consecutive", n, residual)
        checks.append({"identity": f"consecutive n={n}", "residual": mp.nstr(residual, 12)})
    for p, q in [(3, 5), (3, 8), (6, 35), (4, 17), (7, 11)]:
        residual = abs(j_integral(p, q) + j_integral(q, p) - log2 ** 2)
        assert residual < tolerance, ("reciprocity", p, q, residual)
        checks.append({"identity": f"reciprocity {p}/{q}", "residual": mp.nstr(residual, 12)})
    return {"decimal_precision": dps, "tolerance": mp.nstr(tolerance, 5), "checks": checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=401)
    parser.add_argument("--rank-limit", type=int, default=101)
    parser.add_argument("--dps", type=int, default=100)
    parser.add_argument("--output", type=Path, default=Path("verification_j.json"))
    args = parser.parse_args()
    result = {"exact_group_checks": group_checks(args.limit, args.rank_limit),
              "independent_quadrature": numeric_checks(args.dps)}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Passed {result['exact_group_checks']['odd_conductor_zero_tests']} exact zero tests;")
    print(f"passed exact span/rank comparisons through q={args.rank_limit};")
    print(f"passed {len(result['independent_quadrature']['checks'])} quadrature checks at {args.dps} digits.")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
