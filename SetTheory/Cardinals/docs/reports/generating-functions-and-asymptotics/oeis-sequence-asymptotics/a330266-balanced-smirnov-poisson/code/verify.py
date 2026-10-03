#!/usr/bin/env python3
"""Exact verification for fixed-multiplicity shuffle counts.

Run from the archive root:
    python code/verify.py

The exact enumerator uses only the Python standard library.  It writes
``data/verification.csv`` and ``data/standard_deck.txt``.
"""

from __future__ import annotations

import csv
from decimal import Decimal, getcontext
from math import comb, factorial
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
DATA.mkdir(exist_ok=True)
getcontext().prec = 80


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def poly_pow(base: list[int], exponent: int) -> list[int]:
    if exponent < 0:
        raise ValueError("exponent must be nonnegative")
    result = [1]
    x = base[:]
    n = exponent
    while n:
        if n & 1:
            result = poly_mul(result, x)
        n >>= 1
        if n:
            x = poly_mul(x, x)
    return result


def reciprocal_rook_polynomial(k: int) -> list[int]:
    """Coefficients of C_k(z)=sum (-1)^m m! C(k,m) C(k-1,m) z^m."""
    if k < 2:
        raise ValueError("k must be at least 2")
    return [
        (-1) ** m * factorial(m) * comb(k, m) * comb(k - 1, m)
        for m in range(k)
    ]


def labeled_count(n: int, k: int) -> int:
    """Return B_{n,k} exactly using the finite inclusion-exclusion formula."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    coeffs = poly_pow(reciprocal_rook_polynomial(k), n)
    total = k * n
    return sum(c * factorial(total - m) for m, c in enumerate(coeffs))


def probability(n: int, k: int) -> Decimal:
    return Decimal(labeled_count(n, k)) / Decimal(factorial(k * n))


def exp_decimal(x: Decimal) -> Decimal:
    return x.exp()


def multiplicative_coefficients(k: int) -> tuple[Decimal, Decimal, Decimal]:
    kd = Decimal(k)
    lam = Decimal(k - 1)
    alpha = -(lam * lam) / (2 * kd)
    beta = (lam * lam * Decimal(3 * k * k - 14 * k + 7)) / (24 * kd * kd)
    gamma = -(lam**4 * Decimal(k * k - 10 * k + 17)) / (48 * kd**3)
    return alpha, beta, gamma


def normalized_approximation(n: int, k: int) -> Decimal:
    alpha, beta, gamma = multiplicative_coefficients(k)
    nd = Decimal(n)
    return Decimal(1) + alpha / nd + beta / nd**2 + gamma / nd**3


def check_prefix(k: int, expected: Iterable[int]) -> None:
    got = [labeled_count(n, k) for n, _ in enumerate(expected)]
    expected_list = list(expected)
    if got != expected_list:
        raise AssertionError(f"k={k}: expected {expected_list}, got {got}")


def main() -> None:
    check_prefix(2, [1, 0, 8, 240, 13824, 1263360, 168422400])
    check_prefix(3, [1, 0, 72, 37584, 53529984, 152458744320])
    check_prefix(
        4,
        [
            1,
            0,
            1152,
            15095808,
            751480602624,
            93995798935633920,
            25111340235557122867200,
        ],
    )

    deck_count = labeled_count(13, 4)
    expected_deck = int(
        "3668033946384704437729512814619767610579526911188666362431432294400"
    )
    if deck_count != expected_deck:
        raise AssertionError("standard-deck count mismatch")

    rows: list[dict[str, str | int]] = []
    for k in range(2, 7):
        for n in (5, 10, 20, 50):
            p = probability(n, k)
            normalized = p * exp_decimal(Decimal(k - 1))
            approximation = normalized_approximation(n, k)
            rows.append(
                {
                    "k": k,
                    "n": n,
                    "B_nk": str(labeled_count(n, k)),
                    "probability": str(p),
                    "exp(k-1)*probability": str(normalized),
                    "third_order_normalized_approximation": str(approximation),
                    "signed_residual": str(normalized - approximation),
                }
            )

    with (DATA / "verification.csv").open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    p = Decimal(deck_count) / Decimal(factorial(52))
    n = Decimal(13)
    e_minus_3 = exp_decimal(Decimal(-3))
    alpha = Decimal(-9) / 8
    beta = Decimal(-3) / 128
    gamma = Decimal(189) / 1024
    log1 = Decimal(-9) / 8
    log2 = Decimal(-21) / 32
    log3 = Decimal(-81) / 256
    lines = [
        f"B_13,4 = {deck_count}",
        f"exact probability = {p}",
        f"exp(-3) = {e_minus_3}",
        f"multiplicative through n^-1 = {e_minus_3 * (1 + alpha / n)}",
        f"multiplicative through n^-2 = {e_minus_3 * (1 + alpha / n + beta / n**2)}",
        f"multiplicative through n^-3 = {e_minus_3 * (1 + alpha / n + beta / n**2 + gamma / n**3)}",
        "logarithmic through n^-3 = "
        + str(exp_decimal(Decimal(-3) + log1 / n + log2 / n**2 + log3 / n**3)),
        "",
        "All prefix and exact deck checks passed.",
    ]
    (DATA / "standard_deck.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")

    print("All exact checks passed.")
    print(f"Wrote {DATA / 'verification.csv'}")
    print(f"Wrote {DATA / 'standard_deck.txt'}")


if __name__ == "__main__":
    main()
