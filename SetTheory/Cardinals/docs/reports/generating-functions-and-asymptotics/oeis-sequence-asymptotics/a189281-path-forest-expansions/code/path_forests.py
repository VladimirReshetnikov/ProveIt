#!/usr/bin/env python3
"""Exact coefficients and enumeration for fixed-offset permutation avoidance.

Standard-library-only implementation of the formulas proved in the accompanying
article. Coefficients are exact fractions; no conjectured recurrence is used.
Run `python path_forests.py --order 16 --output ../data/coefficients_order16.json`.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
from typing import Iterator, Sequence

Profile = tuple[int, ...]  # b_2, b_3, ...; absent terminal entries are zero.


def partitions(n: int, largest: int | None = None) -> Iterator[tuple[int, ...]]:
    """Integer partitions, in nonincreasing order; the partition of zero is ()."""
    if n < 0:
        raise ValueError('n must be nonnegative')
    if n == 0:
        yield ()
        return
    for p in range(min(n, n if largest is None else largest), 0, -1):
        for tail in partitions(n - p, p):
            yield (p,) + tail


def multiply(a: Sequence[int], b: Sequence[int], order: int) -> list[int]:
    out = [0] * (order + 1)
    for i, x in enumerate(a[:order + 1]):
        if x:
            for j, y in enumerate(b[:order + 1 - i]):
                out[i + j] += x * y
    return out


def linear_product(start: int, length: int, order: int) -> list[int]:
    out = [1] + [0] * order
    for a in range(start, start + length):
        for j in range(order, 0, -1):
            out[j] -= a * out[j - 1]
    return out


def rising(a: int, length: int) -> int:
    value = 1
    for i in range(length):
        value *= a + i
    return value


def falling(a: int, length: int) -> int:
    value = 1
    for i in range(length):
        value *= a - i
    return value


def statistics(b: Profile) -> tuple[int, int, int]:
    c = sum(b)
    k = sum((i + 1) * count for i, count in enumerate(b))
    return c, k, k + c


def profile_factorial(b: Profile) -> int:
    value = 1
    for count in b:
        value *= factorial(count)
    return value


def edge_profiles(k: int) -> Iterator[Profile]:
    for partition in partitions(k):
        counts = [0] * max(partition, default=0)
        for edge_length in partition:
            counts[edge_length - 1] += 1
        yield tuple(counts)


def defect_profiles(d: int) -> Iterator[Profile]:
    # Here the returned entries are beta_3, beta_4, ... rather than b_2, ... .
    for partition in partitions(d):
        counts = [0] * max(partition, default=0)
        for defect in partition:
            counts[defect - 1] += 1
        yield tuple(counts)


def elementary_profile(b: Profile, order: int) -> list[int]:
    out = [1] + [0] * order
    for q, count in enumerate(b, 1):
        out = multiply(out, [comb(count, h) * q**h
                             for h in range(min(count, order) + 1)], order)
    return out


@lru_cache(maxsize=None)
def normalized_f(r: int, b: Profile, order: int) -> tuple[int, ...]:
    """Coefficients of n^{-c} F_r(n;b), with x = 1/n."""
    c, k, _ = statistics(b)
    elementary = elementary_profile(b, order)
    out = [0] * (order + 1)
    for h in range(min(c, order) + 1):
        scale = (-1)**h * rising(r - 1, h) * elementary[h]
        if scale:
            for j, value in enumerate(linear_product(k + h, c - h, order - h)):
                out[h + j] += scale * value
    return tuple(out)


@lru_cache(maxsize=None)
def inverse_denominator(v: int, order: int) -> tuple[int, ...]:
    out = [1] + [0] * order
    for a in range(v):
        for j in range(1, order + 1):
            out[j] += a * out[j - 1]
    return tuple(out)


@lru_cache(maxsize=None)
def profile_coefficient(r: int, s: int, b: Profile, order: int) -> int:
    _, _, v = statistics(b)
    numerator = multiply(normalized_f(r, b, order), normalized_f(s, b, order), order)
    return multiply(numerator, inverse_denominator(v, order), order)[order]


def correction_polynomials(order: int, r: int = 2, s: int = 2,
                           theta: int = 1) -> list[list[Fraction]]:
    """B_0(u), ..., B_order(u), each stored in ascending powers of u."""
    if order < 0 or min(r, s) < 1 or theta not in (1, 2):
        raise ValueError('Require order >= 0, r,s >= 1, theta in {1,2}')
    result = []
    for J in range(order + 1):
        polynomial = [Fraction(0)] * (2 * J + 1)
        for d in range(J + 1):
            for beta in defect_profiles(d):
                C = sum(beta)
                K = sum((i + 2) * count for i, count in enumerate(beta))
                denominator = profile_factorial(beta)
                j = J - d
                differences = [profile_coefficient(r, s, (m,) + beta, j)
                               for m in range(2 * j + 1)]
                for t in range(2 * j + 1):
                    polynomial[K + t] += Fraction(
                        differences[0] * theta**(C + t),
                        denominator * factorial(t))
                    differences = [b - a for a, b in zip(differences, differences[1:])]
        while len(polynomial) > 1 and polynomial[-1] == 0:
            polynomial.pop()
        result.append(polynomial)
    return result


def avoidance_coefficients(polynomials: Sequence[Sequence[Fraction]]) -> list[Fraction]:
    return [sum(((-1)**j * a for j, a in enumerate(poly)), Fraction(0))
            for poly in polynomials]


def stable_F(n: int, r: int, b: Profile) -> int:
    """Integer evaluation of F_r. Its combinatorial meaning requires stability."""
    c, k, _ = statistics(b)
    elementary = elementary_profile(b, c)
    return sum((-1)**h * rising(r - 1, h) * elementary[h]
               * falling(n - k - h, c - h) for h in range(c + 1))


def stable_moments(n: int, r: int, s: int, theta: int,
                   cutoff: int) -> list[Fraction]:
    """E binom(X,k), 0<=k<=cutoff, for standard offset forests.

    Rejects parameters outside the sufficient exact stabilization range.
    """
    if min(r, s) < 1 or theta not in (1, 2) or cutoff < 0:
        raise ValueError('Invalid parameters')
    if cutoff > min(n // r, n // s, n // 2):
        raise ValueError('Cutoff lies outside the exact stabilization range')
    facts = [factorial(i) for i in range(n + 1)]
    moments = []
    for k in range(cutoff + 1):
        numerator = 0
        for b in edge_profiles(k):
            c, _, v = statistics(b)
            fr, fs = stable_F(n, r, b), stable_F(n, s, b)
            bf = profile_factorial(b)
            assert fr % bf == 0
            numerator += theta**c * (fr // bf) * fs * facts[n - v]
        moments.append(Fraction(numerator, facts[n]))
    return moments


@lru_cache(maxsize=None)
def path_tilings(length: int) -> dict[tuple[int, ...], int]:
    """Exact multiset-of-tiles polynomial of a single path; no stability used."""
    out = {}
    for p in partitions(length):
        value = factorial(len(p))
        for count in Counter(p).values():
            value //= factorial(count)
        out[p] = value
    return out


def forest_tilings(lengths: Sequence[int]) -> dict[tuple[int, ...], int]:
    out = {(): 1}
    for length in lengths:
        if length < 0:
            raise ValueError('Path lengths cannot be negative')
        new: defaultdict[tuple[int, ...], int] = defaultdict(int)
        for a, coefficient_a in out.items():
            for b, coefficient_b in path_tilings(length).items():
                new[tuple(sorted(a + b, reverse=True))] += coefficient_a * coefficient_b
        out = dict(new)
    return out


def offset_lengths(n: int, r: int) -> tuple[int, ...]:
    return tuple(n // r + (i < n % r) for i in range(r))


def exact_distribution(n: int, r: int = 2, s: int = 2,
                       theta: int = 1) -> list[int]:
    """Exact numbers of permutations with X=j via full tiling inclusion-exclusion."""
    if n < 0 or min(r, s) < 1 or theta not in (1, 2):
        raise ValueError('Invalid parameters')
    left = forest_tilings(offset_lengths(n, r))
    right = forest_tilings(offset_lengths(n, s))
    binomial_moments = [0] * (n + 1)
    for tiles, a in left.items():
        b = right.get(tiles, 0)
        if not b:
            continue
        k = n - len(tiles)
        c = sum(length > 1 for length in tiles)
        weight = 1
        for count in Counter(tiles).values():
            weight *= factorial(count)
        binomial_moments[k] += theta**c * a * b * weight
    distribution = [sum((-1)**(k - j) * comb(k, j) * binomial_moments[k]
                        for k in range(j, n + 1)) for j in range(n + 1)]
    assert min(distribution) >= 0 and sum(distribution) == factorial(n)
    return distribution


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=16)
    parser.add_argument('--r', type=int, default=2)
    parser.add_argument('--s', type=int, default=2)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = {}
    for theta in (1, 2):
        polynomials = correction_polynomials(args.order, args.r, args.s, theta)
        cs = avoidance_coefficients(polynomials)
        data[str(theta)] = {'B': [[str(a) for a in row] for row in polynomials],
                            'c': [str(a) for a in cs]}
        print(f'theta={theta}, r={args.r}, s={args.s}:')
        print(', '.join(map(str, cs)))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
