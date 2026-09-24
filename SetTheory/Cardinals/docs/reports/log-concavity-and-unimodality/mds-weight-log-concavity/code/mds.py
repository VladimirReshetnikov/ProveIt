#!/usr/bin/env python3
"""Exact MDS weight enumerators and the criteria proved in article.tex.

Only the Python standard library is needed (Python 3.9+).
Parameters are formal: no existence test for an MDS code is performed, and q
need not be a prime power. A nonnegative formal weight enumerator does not
establish that a code exists.
"""
from __future__ import annotations
import argparse
import json
from math import comb
from typing import Sequence


def validate(n: int, k: int, q: int) -> None:
    if not all(isinstance(x, int) for x in (n, k, q)):
        raise TypeError("n, k, and q must be integers")
    if not 1 <= k <= n or q < 2:
        raise ValueError("Require 1 <= k <= n and q >= 2")


def weights(n: int, k: int, q: int) -> list[int]:
    """Return the formal full distribution [A_0,...,A_n], using integers."""
    validate(n, k, q)
    d = n - k + 1
    a = [0] * (n + 1)
    a[0] = 1
    b = 1
    for s in range(k):
        if s:
            b = (q - 1) * b + (-1) ** s * comb(d + s - 2, s)
        a[d + s] = (q - 1) * comb(n, d + s) * b
    return a


def weights_inclusion_exclusion(n: int, k: int, q: int) -> list[int]:
    """Independent O(k^2) implementation of the usual alternating formula."""
    validate(n, k, q)
    d = n - k + 1
    a = [0] * (n + 1)
    a[0] = 1
    for w in range(d, n + 1):
        a[w] = comb(n, w) * sum(
            (-1) ** j * comb(w, j) * (q ** (w - d + 1 - j) - 1)
            for j in range(w - d + 1)
        )
    return a


def failures(a: Sequence[int]) -> list[dict[str, int]]:
    """Find failures after deleting zero coefficients, retaining A_0."""
    if any(x < 0 for x in a):
        raise ValueError("Negative formal coefficients: not a weight distribution")
    support = [(w, x) for w, x in enumerate(a) if x]
    result = []
    for i in range(1, len(support) - 1):
        w, x = support[i]
        delta = x * x - support[i - 1][1] * support[i + 1][1]
        if delta < 0:
            result.append({"weight": w, "difference": delta})
    return result


def twice_quadratic(n: int, k: int, q: int) -> int:
    """2 P_{n,k}(q); its sign decides the q>d case for d>=2,k>=3."""
    validate(n, k, q)
    d = n - k + 1
    b = k * (d * d + 2 * d - 1) + 2
    return 2 * (n + 1) * q * q - 2 * b * q + d * b


def prediction(n: int, k: int, q: int) -> bool:
    """Complete conditional criterion; never asserts existence of a code."""
    validate(n, k, q)
    d = n - k + 1
    if k == 1 or d == 1:
        return True
    if q < d:
        raise ValueError("For k>=2, q<d forces A_(d+1)<0 and is impossible")
    if k == 2:
        return True
    if q > d:
        return twice_quadratic(n, k, q) >= 0
    if d == 2:  # binary single-parity-check distribution
        return True
    return k <= 4 or (k == 5 and d >= 9)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("k", type=int)
    parser.add_argument("q", type=int)
    args = parser.parse_args()
    try:
        a = weights(args.n, args.k, args.q)
        predicted = prediction(args.n, args.k, args.q)
        fs = failures(a)
    except (TypeError, ValueError) as exc:
        parser.error(str(exc))
    result = {
        "n": args.n, "k": args.k, "d": args.n - args.k + 1, "q": args.q,
        "formal_parameters_only": True,
        "compressed_distribution": [
            {"weight": w, "count": x} for w, x in enumerate(a) if x
        ],
        "theorem_predicts_log_concave": predicted,
        "directly_log_concave": not fs,
        "failures": fs,
        "total": sum(a), "expected_total": args.q ** args.k,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
