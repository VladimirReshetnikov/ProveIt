#!/usr/bin/env python3
"""Exact finite checks for article.tex. Requires Python 3.9+, standard library only.

These tests do not verify arbitrary Hahn supports, class maps, or nondefinability.
All power-series computations take place modulo T**(N+1). Sparse rank-two
examples use X^(a,0) * T^n, T = X^(0,-1), with n >= 0. This truncation is
stable under all downward exponent shifts performed by the tested maps.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as Q
import json
from pathlib import Path
import platform
import random
from typing import Dict, List, Tuple

Series = List[Q]
Sparse = Dict[Tuple[Q, int], Q]
COUNTS: Counter = Counter()


def check(condition: bool, category: str, detail: str = "") -> None:
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] += 1


def coefficients_equal(a: Series, b: Series, category: str) -> None:
    check(len(a) == len(b), category)
    for n, (x, y) in enumerate(zip(a, b)):
        check(x == y, category, f"coefficient {n}: {x} != {y}")


def mul(a: Series, b: Series, nmax: int) -> Series:
    out = [Q(0)] * (nmax + 1)
    for i, x in enumerate(a[:nmax + 1]):
        if x:
            for j, y in enumerate(b[:nmax + 1 - i]):
                if y:
                    out[i + j] += x * y
    return out


def binom(a: Q, n: int) -> Q:
    out = Q(1)
    for j in range(n):
        out *= (a - j) / (j + 1)
    return out


def power_binomial(f: Series, a: Q, nmax: int) -> Series:
    """F**a by sum binom(a,j) (F-1)**j; independent of power_recurrence."""
    if f[0] != 1:
        raise ValueError("Expected constant coefficient 1")
    e = (f + [Q(0)] * nmax)[:nmax + 1]
    e[0] = Q(0)
    out = [Q(0)] * (nmax + 1)
    ej = [Q(1)] + [Q(0)] * nmax
    for j in range(nmax + 1):
        bj = binom(a, j)
        for n, value in enumerate(ej):
            out[n] += bj * value
        ej = mul(ej, e, nmax)
    return out


def power_recurrence(f: Series, a: Q, nmax: int) -> Series:
    """F*A' = a*F'*A, A(0)=1: n*A_n = sum(((a+1)j-n) F_j A_(n-j))."""
    if f[0] != 1:
        raise ValueError("Expected constant coefficient 1")
    out = [Q(1)] + [Q(0)] * nmax
    for n in range(1, nmax + 1):
        out[n] = sum(
            (((a + 1) * j - n) * f[j] * out[n - j]
             for j in range(1, min(n + 1, len(f)))), Q(0)
        ) / n
    return out


def sparse_add(f: Sparse, g: Sparse, sign: int = 1) -> Sparse:
    out = dict(f)
    for key, value in g.items():
        out[key] = out.get(key, Q(0)) + sign * value
    return {key: value for key, value in out.items() if value}


def sparse_mul(f: Sparse, g: Sparse, nmax: int) -> Sparse:
    out: Sparse = {}
    for (a, n), x in f.items():
        for (b, m), y in g.items():
            if n + m <= nmax:
                key = (a + b, n + m)
                out[key] = out.get(key, Q(0)) + x * y
    return {key: value for key, value in out.items() if value}


def twist(f: Sparse, c: Q, base: Series, nmax: int) -> Sparse:
    """lambda(a,b) = c*a, h=(0,1); input key (a,n) denotes exponent (a,-n)."""
    out: Sparse = {}
    powers = {a: power_recurrence(base, c * a, nmax) for a, _ in f}
    for (a, n), value in f.items():
        if n < 0:
            raise ValueError("This finite checker requires nonnegative T degree")
        for j in range(nmax - n + 1):
            delta = value * powers[a][j]
            if delta:
                key = (a, n + j)
                out[key] = out.get(key, Q(0)) + delta
    return {key: value for key, value in out.items() if value}


def leading(f: Sparse) -> Tuple[Tuple[Q, int], Q]:
    if not f:
        raise ValueError("Zero has no leading term")
    key = max(f, key=lambda an: (an[0], -an[1]))
    return key, f[key]


def sign_of_exponent(key: Tuple[Q, int]) -> int:
    a, n = key
    if a:
        return 1 if a > 0 else -1
    return -1 if n > 0 else 0


def random_sparse(rng: random.Random) -> Sparse:
    out: Sparse = {}
    for _ in range(rng.randint(2, 8)):
        key = (Q(rng.randint(-3, 3), rng.randint(1, 3)), rng.randint(0, 4))
        out[key] = out.get(key, Q(0)) + Q(rng.randint(-4, 4), rng.randint(1, 3))
    return {key: value for key, value in out.items() if value}


def test_formal_powers() -> None:
    nmax = 14
    bases = [list(map(Q, p)) for p in
             ([1, 1], [1, 0, 2, -3], [1, -1, 0, 0, 1], [1, 0, 0, 1, 0, 0, 2])]
    exponents = sorted({Q(a, b) for a in range(-4, 5) for b in range(1, 4)})
    one = [Q(1)] + [Q(0)] * nmax
    for f in bases:
        cache = {a: power_recurrence(f, a, nmax) for a in exponents}
        for a in exponents:
            coefficients_equal(cache[a], power_binomial(f, a, nmax),
                               "independent_power_algorithms")
            coefficients_equal(mul(cache[a], power_recurrence(f, -a, nmax), nmax),
                               one, "formal_inverse")
        for a in exponents:
            for b in exponents:
                coefficients_equal(mul(cache[a], cache[b], nmax),
                                   power_recurrence(f, a + b, nmax),
                                   "formal_additive_composition")
    for a in exponents:
        coefficients_equal(power_recurrence([Q(1), Q(1)], a, nmax),
                           [binom(a, n) for n in range(nmax + 1)],
                           "binomial_coefficients")


def test_rank_two() -> None:
    rng = random.Random(23092026)
    nmax = 13
    bases = [list(map(Q, f)) for f in ([1, 1], [1, 0, 2, -1], [1, 0, 0, -3])]
    for case in range(120):
        f, g = random_sparse(rng), random_sparse(rng)
        c, d = Q(rng.randint(1, 4), rng.randint(1, 3)), Q(rng.randint(-4, 4), 3)
        base = bases[case % len(bases)]
        sf = twist(f, c, base, nmax)
        check(twist(sf, -c, base, nmax) == f, "rank_two_inverse")
        check(twist(twist(f, d, base, nmax), c, base, nmax)
              == twist(f, c + d, base, nmax), "rank_two_composition")
        check(twist(sparse_mul(f, g, nmax), c, base, nmax)
              == sparse_mul(sf, twist(g, c, base, nmax), nmax),
              "rank_two_multiplicativity")
        check(sf.get((Q(0), 0), Q(0)) == f.get((Q(0), 0), Q(0)),
              "constant_coefficient")
        for sign in (-1, 0, 1):
            restricted = {key: value for key, value in f.items()
                          if sign_of_exponent(key) == sign}
            left = twist(restricted, c, base, nmax)
            right = {key: value for key, value in sf.items()
                     if sign_of_exponent(key) == sign}
            check(left == right, "signed_support_projection")
        if f:
            check(leading(sf) == leading(f), "leading_term_fixed")
        moved = {key: value for key, value in f.items() if key[0] != 0}
        delta = sparse_add(sf, f, -1)
        check(bool(delta) == bool(moved), "fixed_support_kernel")
        if moved:
            (a, n), value = leading(moved)
            m = next(j for j in range(1, len(base)) if base[j])
            check(leading(delta) == ((a, n + m), value * c * a * base[m]),
                  "exact_first_displacement")
        fixed = {(Q(0), n): Q((-1) ** n, n + 1) for n in range(5)}
        check(twist(fixed, c, base, nmax) == fixed, "fixed_subfield_examples")
        check(twist(f, 3 * c, base, nmax) == f if not moved
              else twist(f, 3 * c, base, nmax) != f, "no_sample_period_three")


def poly2_mul(f, g):
    out = {}
    for (a, b), x in f.items():
        for (c, d), y in g.items():
            key = (a + c, b + d)
            # Only positions capable of reaching the target (1,0) are needed.
            if key[0] <= 1 and key[1] <= 0:
                out[key] = out.get(key, Q(0)) + x * y
    return {key: value for key, value in out.items() if value}


def test_first_forbidden_shift() -> None:
    # Shifts (0,1),(0,2) are infinitesimal to g=(1,0); (1,0) is not.
    for q in (Q(1, 2), Q(1, 3), Q(2, 5), Q(3, 7)):
        for a in range(-2, 3):
            for b in range(-2, 3):
                for c in (-3, -1, 1, 3):
                    e = {(0, 1): Q(a), (0, 2): Q(b), (1, 0): Q(c)}
                    ej = {(0, 0): Q(1)}
                    coeff = Q(0)
                    for n in range(9):
                        coeff += binom(q, n) * ej.get((1, 0), Q(0))
                        ej = poly2_mul(ej, e)
                    check(coeff == q * c, "least_bad_shift_coefficient")
                    check(q - 1 < 0, "rational_root_crosses_zero")


def test_noncommutative_example() -> None:
    def sig(p):
        return lambda x, y, z: p(x, y * (1 + 1 / x), z)
    def siginv(p):
        return lambda x, y, z: p(x, y / (1 + 1 / x), z)
    def tau(p):
        return lambda x, y, z: p(x, y, z * (1 + 1 / y))
    def tauinv(p):
        return lambda x, y, z: p(x, y, z / (1 + 1 / y))
    zfun = lambda x, y, z: z
    st, ts = sig(tau(zfun)), tau(sig(zfun))
    commutator = sig(tau(siginv(tauinv(zfun))))
    for xx in range(2, 9):
        for yy in range(3, 10):
            for zz in range(5, 9):
                x, y, z = Q(xx), Q(yy), Q(zz)
                u = 1 + 1 / x
                check(st(x, y, z) - ts(x, y, z) == -z / (x * y * u),
                      "noncommutative_difference")
                check(commutator(x, y, z) == z * (1 + 1 / (y * u)) / (1 + 1 / y),
                      "commutator_formula")
                check(commutator(x, y, z) != z, "commutator_nonidentity_samples")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    test_formal_powers()
    test_rank_two()
    test_first_forbidden_shift()
    test_noncommutative_example()
    report = {
        "status": "passed",
        "python": platform.python_version(),
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "total_assertions": sum(COUNTS.values()),
        "assertions_by_category": dict(sorted(COUNTS.items())),
        "seed": 23092026,
        "arithmetic": "fractions.Fraction; no floating-point approximation",
        "formal_power_truncation_degree": 14,
        "rank_two_truncation_degree": 13,
        "limitations": [
            "Finite checks, not a formal proof.",
            "No verification of arbitrary Hahn summability or proper-class constructions.",
            "No verification of model-theoretic nondefinability or novelty.",
            "Noncommutative rational identities tested on exact finite samples; general proofs are in article.tex.",
        ],
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
