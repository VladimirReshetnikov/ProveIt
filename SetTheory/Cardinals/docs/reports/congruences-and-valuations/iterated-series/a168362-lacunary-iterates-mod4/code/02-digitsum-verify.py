#!/usr/bin/env python3
"""Exact independent checks for the lacunary-iteration article.

Uses only the Python standard library. Run from any directory:
    python3 code/verify.py --output data/verification.json
No finite check is used as a premise of a theorem.
"""

from __future__ import annotations

import argparse
import json
from math import comb, factorial
from pathlib import Path


def digit_sum(n: int, p: int) -> int:
    total = 0
    while n:
        total += n % p
        n //= p
    return total


def valuation(n: int, p: int) -> int | None:
    if n == 0:
        return None
    n = abs(n)
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def mul(a: list[int], b: list[int], degree: int, modulus: int = 0) -> list[int]:
    out = [0] * (degree + 1)
    aa = [(i, x) for i, x in enumerate(a[:degree + 1]) if x]
    bb = [(i, x) for i, x in enumerate(b[:degree + 1]) if x]
    for i, x in aa:
        for j, y in bb:
            if i + j > degree:
                break
            out[i + j] += x * y
    return [x % modulus for x in out] if modulus else out


def power(a: list[int], exponent: int, degree: int, modulus: int = 0) -> list[int]:
    result = [1] + [0] * degree
    while exponent:
        if exponent & 1:
            result = mul(result, a, degree, modulus)
        exponent //= 2
        if exponent:
            a = mul(a, a, degree, modulus)
    return result


def next_iterate(a: list[int], p: int, degree: int, modulus: int = 0) -> list[int]:
    """Direct ordinary-series substitution F_p(a), with no digit pruning."""
    result = [0] * (degree + 1)
    term = a[:degree + 1]
    exponent = 1
    while exponent <= degree:
        result = [x + y for x, y in zip(result, term)]
        if modulus:
            result = [x % modulus for x in result]
        exponent *= p
        if exponent <= degree:
            term = power(term, p, degree, modulus)
    return result


def composition(a: list[int], b: list[int], degree: int, modulus: int = 0) -> list[int]:
    result = [0] * (degree + 1)
    term = [1] + [0] * degree
    for coefficient in a[:degree + 1]:
        if coefficient:
            result = [x + coefficient * y for x, y in zip(result, term)]
            if modulus:
                result = [x % modulus for x in result]
        term = mul(term, b, degree, modulus)
    return result


def inverse(a: list[int], degree: int) -> list[int]:
    """Triangular ordinary-series reversion, independent of Hurwitz scaling."""
    assert a[0] == 0 and a[1] == 1
    result = [0, 1] + [0] * (degree - 1)
    for n in range(2, degree + 1):
        result[n] = -composition(a[:n + 1], result[:n + 1], n)[n]
    return result


def seed(p: int, degree: int) -> list[int]:
    result = [0] * (degree + 1)
    exponent = 1
    while exponent <= degree:
        result[exponent] = 1
        exponent *= p
    return result


def check_bound(a: list[int], p: int) -> int:
    checks = 0
    for n, value in enumerate(a[1:], 1):
        if (n - 1) % (p - 1):
            assert value == 0, (p, n, value, "support")
        else:
            w = (digit_sum(n, p) - 1) // (p - 1)
            assert value % (p ** w) == 0, (p, n, value, w)
            assert (factorial(n) * value) % (p ** ((n - 1) // (p - 1))) == 0
        checks += 1
    return checks


def egf_compose(outer: list[int], inner: list[int], degree: int) -> list[int]:
    """Set-partition Bell recurrence; inputs/outputs are exponential coefficients."""
    bell = [[0] * (degree + 1) for _ in range(degree + 1)]
    bell[0][0] = 1
    for n in range(1, degree + 1):
        for k in range(1, n + 1):
            bell[n][k] = sum(
                comb(n - 1, j - 1) * inner[j] * bell[n - j][k - 1]
                for j in range(1, n - k + 2)
            )
    return [sum(outer[k] * bell[n][k] for k in range(n + 1))
            for n in range(degree + 1)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    parser.add_argument("--heatmap", type=Path)
    args = parser.parse_args()
    receipt: dict = {"status": "PASS", "arithmetic": "exact Python integers"}
    total = 0
    sharp = []
    for p in (2, 3, 5, 7):
        degree = 128
        a = [0, 1] + [0] * (degree - 1)
        for m in range(1, 9):
            a = next_iterate(a, p, degree)
            total += check_bound(a, p)
            if m == 2:
                for n in range(2, degree + 1):
                    if a[n] and (n - 1) % (p - 1) == 0:
                        w = (digit_sum(n, p) - 1) // (p - 1)
                        if w > 0 and valuation(a[n], p) == w:
                            sharp.append({"p": p, "m": m, "N": n,
                                          "coefficient": str(a[n]), "valuation": w})
        small = 35
        inv = inverse(seed(p, small), small)
        assert composition(seed(p, small), inv, small) == [0, 1] + [0] * (small - 1)
        total += check_bound(inv, p)
    receipt["valuation_checks"] = total
    receipt["positive_range"] = {"primes": [2, 3, 5, 7], "iterates": [1, 8], "degree": 128}
    receipt["inverse_degree"] = 35
    receipt["sharp_examples"] = sharp[:30]

    bell_checks = 0
    for p in (2, 3, 5):
        degree = 28
        f = seed(p, degree)
        h = [0] * (degree + 1)
        for n in range(1, degree + 1):
            if f[n]:
                h[n] = factorial(n) // p ** ((n - 1) // (p - 1))
        a = [0, 1] + [0] * (degree - 1)
        b = a[:]
        for m in range(1, 5):
            a = next_iterate(a, p, degree)
            b = egf_compose(h, b, degree)
            for n in range(1, degree + 1):
                expected = (factorial(n) * a[n] // p ** ((n - 1) // (p - 1))
                            if (n - 1) % (p - 1) == 0 else 0)
                assert b[n] == expected, ("Bell", p, m, n)
                bell_checks += 1
    receipt["independent_Bell_checks"] = bell_checks

    fuss_checks = 0
    for p in (2, 3, 5, 7, 11):
        for k in range(0, 150):
            n = 1 + (p - 1) * k
            numerator = comb(p * k, k)
            assert numerator % n == 0
            value = numerator // n
            assert valuation(value, p) == (digit_sum(n, p) - 1) // (p - 1)
            fuss_checks += 1
    receipt["Fuss_Catalan_exact_valuation_checks"] = fuss_checks

    # Direct source fixtures: OEIS A168362, A168365 and A168366.
    fixtures = {
        0: [1, 2, 6, 34, 280, 3010, 39984, 634040, 11704548, 246799212],
        -1: [1, 1, 2, 12, 100, 1070, 14116, 222614, 4092964, 86058372],
        1: [1, 3, 12, 75, 650, 7238, 98728, 1597689, 29965770, 639867250],
    }
    degree = 10
    rows = [[0, 1] + [0] * (degree - 1)]
    for m in range(1, degree + 2):
        rows.append(next_iterate(rows[-1], 2, degree))
    for offset, values in fixtures.items():
        assert [rows[n + offset][n] for n in range(1, 11)] == values
    receipt["OEIS_fixture_checks"] = {"A168362": 10, "A168365": 10, "A168366": 10}

    # Test the sufficient period using modular direct iterates, for q=3.
    periods = []
    for p in (2, 3, 5):
        degree, q = 22, 3
        specifications = []
        for n in range(2, degree + 1):
            if (n - 1) % (p - 1):
                continue
            d = (n - 1) // (p - 1)
            w = (digit_sum(n, p) - 1) // (p - 1)
            if w >= q:
                continue
            logd, powerp = 0, p
            while powerp <= d:
                logd += 1
                powerp *= p
            specifications.append((n, p ** (q - w + logd)))
        limit = max(period for n, period in specifications) + 3
        a = [0, 1] + [0] * (degree - 1)
        rows = [a]
        for m in range(limit):
            rows.append(next_iterate(rows[-1], p, degree, p ** q))
        for n, period in specifications:
            for m in range(4):
                assert rows[m][n] == rows[m + period][n], ("period", p, n, m)
            periods.append({"p": p, "q": q, "N": n, "sufficient_period": period})
    receipt["period_checks"] = periods

    for p in (3, 5, 7, 11):
        a = next_iterate(seed(p, 2 * p - 1), p, 2 * p - 1)
        assert a[2 * p - 1] == p
    receipt["odd_prime_counterexamples"] = {"p": [3, 5, 7, 11], "coefficient": "[x^(2p-1)]F_p(F_p(x)) = p"}

    if args.heatmap:
        degree, modulus = 127, 128
        a = [0, 1] + [0] * (degree - 1)
        matrix = []
        for m in range(1, 49):
            a = next_iterate(a, 2, degree, modulus)
            matrix.append([valuation(x, 2) if x else 7 for x in a[1:]])
        args.heatmap.parent.mkdir(parents=True, exist_ok=True)
        args.heatmap.write_text(json.dumps({"prime": 2, "modulus": 128,
            "degrees": [1, degree], "iterates": [1, 48], "cap": 7,
            "valuation_matrix": matrix, "bound": [n.bit_count() - 1 for n in range(1, degree + 1)]}, indent=2) + "\n")
        receipt["heatmap"] = {"degree": degree, "iterates": 48, "modulus": modulus}

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k not in ("sharp_examples", "period_checks")}, indent=2))


if __name__ == "__main__":
    main()
