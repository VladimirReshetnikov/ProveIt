#!/usr/bin/env python3
"""Exact finite checks accompanying the surreal-recurrence research draft.

Python 3.10+, standard library only. These are regression checks for explicit
identities and examples, not proofs of the infinite or universal theorems.
Run: python3 verify.py
"""
from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from math import comb, factorial
from random import Random
from typing import Mapping

Poly = dict[int, Fraction]
COUNTS: Counter[str] = Counter()


def check(condition: bool, family: str, detail: str) -> None:
    if not condition:
        raise AssertionError(f"{family}: {detail}")
    COUNTS[family] += 1


def clean(p: Mapping[int, Fraction | int]) -> Poly:
    return {e: Fraction(c) for e, c in p.items() if c}


def add(*polynomials: Mapping[int, Fraction | int]) -> Poly:
    result: dict[int, Fraction] = defaultdict(Fraction)
    for p in polynomials:
        for e, c in p.items():
            result[e] += c
    return clean(result)


def scale(p: Mapping[int, Fraction | int], c: Fraction | int) -> Poly:
    return clean({e: c * a for e, a in p.items()})


def mul(p: Mapping[int, Fraction | int], q: Mapping[int, Fraction | int]) -> Poly:
    result: dict[int, Fraction] = defaultdict(Fraction)
    for e, a in p.items():
        for f, b in q.items():
            result[e + f] += a * b
    return clean(result)


def power(p: Mapping[int, Fraction | int], n: int) -> Poly:
    if n < 0:
        raise ValueError("The finite-polynomial power requires n >= 0.")
    answer: Poly = {0: Fraction(1)}
    base = clean(p)
    while n:
        if n & 1:
            answer = mul(answer, base)
        n >>= 1
        if n:
            base = mul(base, base)
    return answer


def shift(p: Mapping[int, Fraction | int], n: int) -> Poly:
    return clean({e + n: c for e, c in p.items()})


def coefficient(p: Mapping[int, Fraction | int], e: int) -> Fraction:
    return Fraction(p.get(e, 0))


def falling(n: int, j: int) -> int:
    return 0 if n < j else factorial(n) // factorial(n - j)


def test_coefficient_formula() -> None:
    # q = c(1+epsilon), P(n) = sum_d a_d(t) n^d.  Include negative
    # coefficient exponents, nontrivial principal units, and residual signs.
    cases = [
        (Fraction(2), {1: 1, 3: 2}, [{-2: 3, 1: -1}, {0: 2, 4: 1}]),
        (Fraction(-1), {2: -2, 5: 1}, [{-1: 1, 3: 2}, {}, {0: -3}]),
        (Fraction(3, 2), {1: Fraction(1, 2), 4: -1}, [{0: 2}, {2: 1}]),
    ]
    for ci, (c, eps, coefficients) in enumerate(cases):
        q = scale(add({0: 1}, eps), c)
        min_a = min(e for a in coefficients for e in a)
        max_m = (24 - min_a) // min(eps)
        eps_powers = [power(eps, m) for m in range(max_m + 1)]
        for n in range(19):
            p_n = add(*(scale(a, n**d) for d, a in enumerate(coefficients)))
            direct = mul(p_n, power(q, n))
            for gamma in range(-3, 25):
                rhs = Fraction(0)
                for d, a in enumerate(coefficients):
                    for m, eps_m in enumerate(eps_powers):
                        if m <= n:
                            rhs += n**d * comb(n, m) * coefficient(mul(a, eps_m), gamma)
                rhs *= c**n
                check(coefficient(direct, gamma) == rhs,
                      "unit coefficient formula", f"case={ci}, n={n}, exponent={gamma}")


def test_unit_examples() -> None:
    for n in range(1, 81):
        u = add(power({0: -1, 1: -1}, n), {0: -1})
        check(bool(u) and min(u) == (0 if n % 2 else 1),
              "residual parity valuation", f"n={n}")
    for n in range(45):
        u = add(power({0: 1, 1: 1}, n), {0: -1, 1: -n})
        expected = not u if n < 2 else bool(u) and min(u) == 2
        check(expected, "principal-unit cancellation", f"n={n}")
    for d in range(1, 19):
        for n in range(45):
            c = comb(n, d) if n >= d else 0
            check((c == 0) == (n < d), "unbounded coordinate transients", f"d={d}, n={n}")


def test_rank_two_and_coding() -> None:
    # Exponent (a,b) represents a*omega+b; compare tuples lexicographically.
    for n in range(201):
        check(min((1, 0), (0, n)) == (0, n),
              "higher-rank affine comparison", f"n={n}")
    b = [Fraction((-1)**m * (m*m + 1), m + 1) for m in range(65)]
    a = {(1, -m): c for m, c in enumerate(b) if c}
    for n in range(90):
        u = {(hi, lo + n): c for (hi, lo), c in a.items()}
        expected = b[n] if n < len(b) else Fraction(0)
        check(u.get((1, 0), 0) == expected,
              "omnific coefficient coding", f"rational sequence, n={n}")
        check(all(e > (0, 0) for e in u),
              "omnific coefficient coding", f"positive support, n={n}")
    square_set = {m*m for m in range(11)}
    a = {(1, -m): Fraction(1) for m in square_set}
    for n in range(101):
        u = {(hi, lo + n): c for (hi, lo), c in a.items()}
        check((u.get((1, 0), 0) != 0) == (n in square_set),
              "omnific coefficient coding", f"square-set window, n={n}")


def test_catalan() -> None:
    # Truncated lambda=t*C(t^2); check only degrees whose coefficients
    # cannot depend on the omitted tail.
    lam = {2*k + 1: Fraction(comb(2*k, k), k + 1) for k in range(21)}
    residual = add(mul(lam, lam), scale(shift(lam, -1), -1), {0: 1})
    for exponent in range(40):
        check(coefficient(residual, exponent) == 0,
              "Catalan algebraic identity", f"t^{exponent}")
    for n in range(1, 9):
        lam_n = power(lam, n)
        for k in range(11):
            expected = Fraction(n, n + 2*k) * comb(n + 2*k, k)
            check(coefficient(lam_n, n + 2*k) == expected,
                  "Catalan power coefficients", f"n={n}, k={k}")
        for k in range(11):
            check((1, -n - 2*k) > (0, 0),
                  "declining omnific support", f"n={n}, k={k}")


def test_theta() -> None:
    # Dictionary exponents are powers of an indeterminate Q. The identity
    # is checked as a Laurent polynomial in Q, not at floating-point Q.
    for n in range(101):
        a = n*(n-1)//2
        terms: list[dict[int, int]] = [{a: 1}, {a + n: -1}]
        if n:
            previous = (n-1)*(n-2)//2
            terms.extend([{previous + n - 1: -1}, {previous + 2*n - 1: 1}])
        check(not add(*terms), "partial-theta operator", f"z^{n}")


def test_operator_indexing() -> None:
    random = Random(20260923)
    for trial in range(35):
        terms: dict[tuple[int, int, int], Fraction] = defaultdict(Fraction)
        for _ in range(16):
            key = (random.choice([1, 2, 3]), random.randrange(4), random.randrange(5))
            terms[key] += Fraction(random.randrange(-4, 5), random.randrange(1, 5))
        terms = {key: c for key, c in terms.items() if c}
        a = [Fraction(random.randrange(-5, 6), random.randrange(1, 6)) for _ in range(35)]
        direct: dict[int, Fraction] = defaultdict(Fraction)
        for (lam, j, k), c in terms.items():
            for m in range(j, len(a)):
                direct[m-j+k] += c * a[m] * lam**m * falling(m, j)
        for n in range(4, 29):
            by_shift = Fraction(0)
            for (lam, j, k), c in terms.items():
                s = j-k
                m = n+s
                by_shift += c * lam**(n+s) * falling(n+s, j) * a[m]
            check(direct[n] == by_shift,
                  "mixed-operator coefficient indexing", f"trial={trial}, n={n}")


def test_positive_characteristic() -> None:
    for p in (2, 3, 5, 7):
        for n in range(1, 101):
            first = next(i for i in range(1, n+1) if comb(n, i) % p)
            m, expected = n, 1
            while m % p == 0:
                m //= p
                expected *= p
            check(first == expected,
                  "positive-characteristic boundary", f"p={p}, n={n}")


def main() -> None:
    test_coefficient_formula()
    test_unit_examples()
    test_rank_two_and_coding()
    test_catalan()
    test_theta()
    test_operator_indexing()
    test_positive_characteristic()
    print("Exact finite verification: PASS")
    print("Arithmetic: Python standard-library integers and Fraction; no floating-point tests.")
    print("Scope: finite identities and examples only, not universal or infinite-support proofs.\n")
    for family, count in COUNTS.items():
        print(f"{family}: {count} checks")
    print(f"\nTOTAL: {sum(COUNTS.values())} checks passed.")


if __name__ == "__main__":
    main()
