#!/usr/bin/env python3
"""Exact enumeration, recognition and uniform sampling for Andrasfai graphs.

Python 3.9+, standard library only. Vertex labels are 0,...,3*n-2.
All counts include the empty set. These are labeled subsets, not necklaces.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import random
from fractions import Fraction
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

# Entries are (destination state, emitted membership bit).
EDGES: Tuple[Tuple[Tuple[int, int], ...], ...] = (
    ((0, 0), (1, 1)),
    ((0, 0), (2, 1)),
    ((3, 0),),
    ((1, 0), (1, 1)),
)
Matrix = List[List[int]]


def check_n(n: int) -> None:
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError("n must be a positive integer")


def matrix(y: int = 1) -> Matrix:
    return [[1, y, 0, 0], [1, 0, y, 0], [0, 0, 0, 1], [0, 1 + y, 0, 0]]


def identity() -> Matrix:
    return [[int(i == j) for j in range(4)] for i in range(4)]


def multiply(a: Matrix, b: Matrix) -> Matrix:
    return [[sum(a[i][k] * b[k][j] for k in range(4))
             for j in range(4)] for i in range(4)]


def power(a: Matrix, exponent: int) -> Matrix:
    if exponent < 0:
        raise ValueError("negative matrix exponent")
    result = identity()
    while exponent:
        if exponent & 1:
            result = multiply(result, a)
        a = multiply(a, a)
        exponent >>= 1
    return result


def total(n: int) -> int:
    """Count all mutual-visibility sets, in O(log n) big-integer matrix operations."""
    check_n(n)
    if n == 1:
        return 4
    a = power(matrix(), 3 * n - 1)
    return sum(a[i][i] for i in range(4))


def sequence(count: int) -> List[int]:
    """Return a(1),...,a(count), using the proved recurrence with its proper start."""
    if count < 0:
        raise ValueError("count must be nonnegative")
    values = [4, 21, 127, 749, 4455][:count]
    while len(values) < count:
        values.append(10 * values[-1] - 29 * values[-2]
                      + 32 * values[-3] - 8 * values[-4])
    return values


def polynomial(n: int) -> List[int]:
    """Coefficient list of V_n(y), using labeled-edge dynamic programming."""
    check_n(n)
    if n == 1:
        return [1, 2, 1]
    length = 3 * n - 1
    coefficients = [0] * (length + 1)
    for start in range(4):
        dp = [[0] * (length + 1) for _ in range(4)]
        dp[start][0] = 1
        for t in range(length):
            nxt = [[0] * (length + 1) for _ in range(4)]
            for state, edges in enumerate(EDGES):
                for target, bit in edges:
                    for k in range(t + 1):
                        nxt[target][k + bit] += dp[state][k]
            dp = nxt
        for k in range(length + 1):
            coefficients[k] += dp[start][k]
    while len(coefficients) > 1 and coefficients[-1] == 0:
        coefficients.pop()
    return coefficients


def binomial(n: int, k: int) -> int:
    return math.comb(n, k) if 0 <= k <= n else 0


def polynomial_blocks(n: int) -> List[int]:
    """Independent exact evaluation of the return-block binomial sum."""
    check_n(n)
    if n == 1:
        return [1, 2, 1]
    length = 3 * n - 1
    result = [Fraction(0) for _ in range(2 * n)]
    result[0] = Fraction(1)
    for p in range(1, length // 2 + 1):
        for q in range((length - 2 * p) // 3 + 1):
            j = length - 2 * p - 3 * q
            prefactor = (Fraction(length, p) * binomial(p + q - 1, q)
                         * binomial(j + p - 1, p - 1))
            for b in range(q + 1):
                result[p + q + b] += prefactor * binomial(q, b)
    if any(v.denominator != 1 for v in result):
        raise AssertionError("nonintegral result in block formula")
    return [int(v) for v in result]


def fixed_deficit(n: int, h: int) -> int:
    """Number of sets with 2*n-1-h vertices (for nonempty target size).

    Uses the exact constrained block sum, with inadmissible q omitted.
    Its eventual polynomial expression is valid for n >= max(2, 2*h+1).
    """
    check_n(n)
    if h < 0 or n < 2 or 2 * n - 1 - h <= 0:
        raise ValueError("require n>=2, h>=0, and 2*n-1-h>0")
    delta = 1 + 3 * h
    result = Fraction(0)
    for p in range(1, delta + 1):
        for j in range((delta - p) // 2 + 1):
            rest = delta - p - 2 * j
            if rest % 3:
                continue
            d = rest // 3
            numerator = 3 * n - 1 - 2 * p - j
            if numerator % 3:
                raise AssertionError("unexpected congruence")
            q = numerator // 3
            if q < d:
                continue
            result += (Fraction(3 * n - 1, p) * binomial(p + q - 1, p - 1)
                       * binomial(j + p - 1, p - 1) * binomial(q, d))
    if result.denominator != 1:
        raise AssertionError("nonintegral deficit count")
    return int(result)


def is_visible(n: int, word: Sequence[int]) -> bool:
    """O(n)-time Boolean recognizer; input is a membership word of length 3*n-1."""
    check_n(n)
    length = 3 * n - 1
    if len(word) != length or any(bit not in (0, 1) for bit in word):
        raise ValueError("expected a binary word of length 3*n-1")
    if n == 1:
        return True
    zero = next((i for i, bit in enumerate(word) if not bit), None)
    if zero is None:
        return False
    flags = [False] * length
    previous = zero
    for _ in range(1, length):
        current = (previous + 3) % length
        flags[current] = bool(word[current] and
                              (word[(current - 1) % length] or flags[previous]))
        previous = current
    return not any(flags[i] and word[(i + 1) % length] for i in range(length))


def graph(n: int) -> List[List[int]]:
    check_n(n)
    length = 3 * n - 1
    return [[(i + d) % length for d in range(1, length, 3)] for i in range(length)]


class UniformSampler:
    """Exact sampler with O(n) integer-arithmetic preprocessing and per sample.

    Counts are unbounded Python integers; random choices use randrange, never
    floating-point weights. Cached matrices require O(n^2) bits in total.
    """
    def __init__(self, n: int, rng: Optional[random.Random] = None):
        check_n(n)
        self.n = n
        self.length = 3 * n - 1
        self.rng = rng if rng is not None else random.Random()
        self.powers = [identity()]
        if n > 1:
            m = matrix()
            for _ in range(self.length):
                self.powers.append(multiply(self.powers[-1], m))

    def _choose(self, weights: Sequence[int]) -> int:
        r = self.rng.randrange(sum(weights))
        for index, weight in enumerate(weights):
            if r < weight:
                return index
            r -= weight
        raise AssertionError("unreachable weighted-choice branch")

    def sample(self) -> List[int]:
        if self.n == 1:
            return [self.rng.randrange(2), self.rng.randrange(2)]
        last = self.powers[-1]
        start = self._choose([last[i][i] for i in range(4)])
        state = start
        word = []
        for remaining in range(self.length - 1, -1, -1):
            edges = EDGES[state]
            choice = self._choose([self.powers[remaining][target][start]
                                   for target, _ in edges])
            state, bit = edges[choice]
            word.append(bit)
        assert state == start
        return word


def write_data(destination: Path, count: int = 250, rows: int = 50) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    values = sequence(count)
    with (destination / "b391632_extended.txt").open("w", encoding="utf-8") as f:
        f.write("# Derived from the proof in article.pdf; n a(n), 1-based.\n")
        for n, value in enumerate(values, 1):
            f.write(f"{n} {value}\n")
    with (destination / "visibility_coefficients.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "vertices", "cardinality", "count"])
        for n in range(1, rows + 1):
            for k, value in enumerate(polynomial(n)):
                writer.writerow([n, 3 * n - 1, k, value])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=8)
    parser.add_argument("--sample", action="store_true")
    parser.add_argument("--write-data", type=Path)
    args = parser.parse_args()
    if args.write_data:
        write_data(args.write_data)
    else:
        output = {"n": args.n, "total": total(args.n), "coefficients": polynomial(args.n)}
        if args.sample:
            output["sample"] = UniformSampler(args.n, random.Random(20260919)).sample()
        print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
