#!/usr/bin/env python3
"""Deterministic finite checks for the coarse-core manuscript.

These tests verify finite arithmetic/coding facts, not infinitary existence,
Turing reducibility, oracle-jump identities, or novelty. No third-party modules.
"""
from __future__ import annotations

import argparse
import bisect
import functools
import itertools
import json
import random
import sys
from pathlib import Path
from typing import Callable

COUNTS: dict[str, int] = {}
SCOPES: dict[str, str] = {}


def check(name: str, condition: bool, detail: object = "") -> None:
    COUNTS[name] = COUNTS.get(name, 0) + 1
    if not condition:
        raise AssertionError(f"{name}: {detail!r}")


def pair(n: int, t: int) -> int:
    if n < 0 or t < 0:
        raise ValueError("Coordinates must be nonnegative")
    return (1 << n) * (2 * t + 1) - 1


def unpair(x: int) -> tuple[int, int]:
    if x < 0:
        raise ValueError("Input must be nonnegative")
    y = x + 1
    n = (y & -y).bit_length() - 1
    return n, ((y >> n) - 1) // 2


def block(k: int) -> range:
    if k < 0:
        raise ValueError("Block index must be nonnegative")
    return range((1 << k) - 1, (1 << (k + 1)) - 1)


def level(t: int) -> int:
    if t < 0:
        raise ValueError("Row coordinate must be nonnegative")
    return (t + 1).bit_length() - 1


def encode(array: Callable[[int, int], int], x: int) -> int:
    n, t = unpair(x)
    return array(n, level(t))


def decode(oracle: Callable[[int], int], n: int, k: int) -> int:
    b = block(k)
    return int(2 * sum(oracle(pair(n, t)) for t in b) > len(b))


def sample_bit(n: int, k: int) -> int:
    """A deterministic total computable sample array, not an oracle simulation."""
    z = ((n + 5) * 0x9E3779B1) ^ ((k + 17) * 0x85EBCA77)
    return (z ^ (z >> 9) ^ (z >> 17)).bit_count() & 1


def code_error_positions(masks: dict[int, set[int]]) -> list[int]:
    return sorted({pair(n, t) for n, ks in masks.items() for k in ks for t in block(k)})


def first_column_cost(masks: dict[int, set[int]], m: int) -> int:
    return sum(1 << k for n, ks in masks.items() if n < m for k in ks)


def verify_counts() -> None:
    name = "pairing_and_blocks"
    SCOPES[name] = "Pairing inverse for x < 32768 and 14 x 129 coordinate pairs; blocks k < 14."
    for x in range(32768):
        check(name, pair(*unpair(x)) == x, x)
    for n in range(14):
        for t in range(129):
            check(name, unpair(pair(n, t)) == (n, t), (n, t))
    for k in range(14):
        b = block(k)
        check(name, len(b) == 1 << k, k)
        for t in b:
            check(name, level(t) == k, (k, t))
    name = "column_and_tail_counts"
    SCOPES[name] = "Every prefix length 0..4096, columns 0..13, and tails 0..14."
    counts = [0] * 15
    for N in range(4097):
        if N:
            n, _ = unpair(N - 1)
            counts[n] += 1
        for n in range(14):
            actual = counts[n]
            expected = (N + (1 << n)) // (1 << (n + 1))
            check(name, actual == expected, (N, n, actual, expected))
        for m in range(15):
            actual = sum(counts[m:])
            check(name, actual == N // (1 << m), (N, m))


def verify_majority() -> None:
    name = "exhaustive_majority_error"
    SCOPES[name] = "All binary words of lengths 1,2,4,8,16 and both constant targets."
    for k in range(5):
        size = 1 << k
        endpoint = 2 * size - 1
        for word in range(1 << size):
            ones = word.bit_count()
            decoded = int(2 * ones > size)
            for target in (0, 1):
                errors = ones if target == 0 else size - ones
                if decoded != target:
                    check(name, 2 * errors >= size and 4 * errors > endpoint,
                          (k, word, target))
                else:
                    check(name, True)


def verify_normalizer() -> None:
    name = "normalizer_and_roundtrip"
    SCOPES[name] = "Rows 0..11, bits 0..11 for exact roundtrip; idempotence on 8 x 8 blocks of a sample oracle."
    coded = functools.lru_cache(maxsize=None)(lambda x: encode(sample_bit, x))
    for n in range(12):
        for k in range(12):
            check(name, decode(coded, n, k) == sample_bit(n, k), (n, k))
            check(name, coded(pair(n, (1 << k) - 1)) == sample_bit(n, k), (n, k))
    oracle = lambda x: (x * x + 7 * x + 19).bit_count() & 1
    decoded = functools.lru_cache(maxsize=None)(lambda n, k: decode(oracle, n, k))
    normal = lambda x: encode(decoded, x)
    for n in range(8):
        for k in range(8):
            check(name, decode(normal, n, k) == decoded(n, k), (n, k))


def verify_error_bounds() -> None:
    name = "finite_masks_tail_bound_and_modulus"
    SCOPES[name] = "160 seeded finite mask arrays, 9 cutoffs, finite prefix samples and modulus samples; integer arithmetic only."
    rng = random.Random(20260928)
    for case in range(160):
        masks = {n: {k for k in range(6) if rng.randrange(5) == 0} for n in range(7)}
        points = code_error_positions(masks)
        check(name, len(points) == first_column_cost(masks, 8), case)
        prefixes = set(range(1, 130)) | {1 << r for r in range(1, 15)}
        prefixes |= {x + 1 for x in points[::max(1, len(points) // 20)]}
        for m in range(9):
            K = first_column_cost(masks, m)
            actual_first = sum(unpair(x)[0] < m for x in points)
            check(name, actual_first == K, (case, m))
            for N in prefixes:
                errors = bisect.bisect_left(points, N)
                check(name, errors <= K + N // (1 << m), (case, m, N))
        for r in range(9):
            K = first_column_cost(masks, r + 1)
            M = (1 << (r + 1)) * (K + 1)
            for N in (M, M + 1, 2 * M, 2 * M + 17):
                errors = bisect.bisect_left(points, N)
                check(name, errors * (1 << r) < N, (case, r, N))
        m0 = case % 7
        tail_masks = {n: ks for n, ks in masks.items() if n >= m0}
        tail_points = code_error_positions(tail_masks)
        for N in prefixes:
            check(name, bisect.bisect_left(tail_points, N) <= N // (1 << m0),
                  (case, m0, N))


def verify_no_cross() -> None:
    name = "finite_no_cross_disagreement"
    SCOPES[name] = "All pairs of three-entry possible-output lists with entries undefined,0,1 (729 rectangles)."
    values = (None, 0, 1)
    lists = list(itertools.product(values, repeat=3))
    for left in lists:
        for right in lists:
            L = {x for x in left if x is not None}
            R = {x for x in right if x is not None}
            splits = any(a != b for a in L for b in R)
            if not splits and L and R:
                check(name, len(L) == len(R) == 1 and L == R, (left, right))
            else:
                check(name, True)


def verify_interleaving() -> None:
    name = "interleaved_rows"
    SCOPES[name] = "12 even and odd rows; 10 decoded bits each; toy convergent odd-row approximations."
    C = lambda n: ((n * 19 + 11) ^ (n >> 1)).bit_count() & 1
    approximation = lambda n, s: C(n) if s >= n + 2 else (C(n) ^ ((s + 1) & 1))
    def rows(j: int, k: int) -> int:
        n, odd = divmod(j, 2)
        if odd:
            return approximation(n, k)
        return sample_bit(n, k) ^ int(k == (n % 4))
    coded = functools.lru_cache(maxsize=None)(lambda x: encode(rows, x))
    for n in range(12):
        for k in range(10):
            check(name, decode(coded, 2 * n, k) == rows(2 * n, k), (n, k))
            check(name, decode(coded, 2 * n + 1, k) == approximation(n, k), (n, k))
        for s in range(n + 2, n + 14):
            check(name, approximation(n, s) == C(n), (n, s))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/verification.json"))
    args = parser.parse_args()
    for test in (verify_counts, verify_majority, verify_normalizer, verify_error_bounds,
                 verify_no_cross, verify_interleaving):
        test()
    result = {
        "status": "passed",
        "scope": "Finite combinatorial verification only; not a proof of infinitary computability statements.",
        "seed": 20260928,
        "python": sys.version.split()[0],
        "total_checks": sum(COUNTS.values()),
        "tests": [{"name": n, "checks": COUNTS[n], "scope": SCOPES[n]} for n in COUNTS],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, OSError, ValueError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
