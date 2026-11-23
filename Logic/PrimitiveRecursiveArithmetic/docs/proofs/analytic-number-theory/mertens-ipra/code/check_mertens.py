#!/usr/bin/env python3
"""Reproduce the finite tables in the paper with integer arithmetic (Python 3.9+)."""
import argparse
import csv
import json
from pathlib import Path
from math import isqrt


def mobius_prefix(limit):
    """Euler's linear sieve, followed by prefix summation."""
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    mu = [0] * (limit + 1)
    primes = []
    composite = bytearray(limit + 1)
    if limit:
        mu[1] = 1
    for i in range(2, limit + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            j = i * p
            if j > limit:
                break
            composite[j] = 1
            if i % p == 0:
                mu[j] = 0
                break
            mu[j] = -mu[i]
    total = 0
    prefix = []
    for value in mu:
        total += value
        prefix.append(total)
    return mu, prefix


def inverse_prefix(limit):
    """Independent check: invert the constant arithmetic function by proper divisors."""
    mu = [0] * (limit + 1)
    if limit:
        mu[1] = 1
    for d in range(1, limit + 1):
        for m in range(2 * d, limit + 1, d):
            mu[m] -= mu[d]
    return mu


def ceil_cuberoot(n):
    low, high = 0, 1 << ((n.bit_length() + 2) // 3)
    while low < high:
        mid = (low + high) // 2
        if mid ** 3 < n:
            low = mid + 1
        else:
            high = mid
    return low


def isolated(n):
    """Evaluate M(n) by the grouped quotient recurrence in the paper."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    b = ceil_cuberoot(n)
    y = min(n, b * b)
    _, small = mobius_prefix(y)
    if n <= y:
        return small[n]
    k = n // (y + 1)
    large = [0] * (k + 1)
    for i in range(k, 0, -1):
        v = n // i
        acc = 1
        left = 2
        while left <= v:
            q = v // left
            right = v // q
            if q <= y:
                weight = small[q]
            else:
                weight = large[i * left]
            acc -= (right - left + 1) * weight
            left = right + 1
        large[i] = acc
    return large[1]


def hyperbola_value(n):
    """Second isolated-value formula; only uses mu and M up to sqrt(n)."""
    if n == 0:
        return 0
    r = isqrt(n)
    mu, prefix = mobius_prefix(r)
    acc = 2 * prefix[r]
    for a in range(1, r + 1):
        if mu[a] == 0:
            continue
        v = n // a
        left = 1
        while left <= r:
            q = v // left
            right = min(r, v // q)
            acc -= mu[a] * q * (prefix[right] - prefix[left - 1])
            left = right + 1
    return acc


def require(condition, description):
    if not condition:
        raise ArithmeticError(description)


def verify(directory):
    directory.mkdir(parents=True, exist_ok=True)
    limit = 10000
    mu, prefix = mobius_prefix(limit)
    require(mu == inverse_prefix(limit), "divisor inversion disagrees with the sieve")
    for n in range(1, 513):
        require(sum(prefix[n // d] for d in range(1, n + 1)) == 1, "floor sum")
        require(isolated(n) == prefix[n], "quotient algorithm")
    powers = [isolated(10 ** j) for j in range(10)]
    require(powers == [hyperbola_value(10 ** j) for j in range(10)], "independent hyperbola formula")
    require(powers == [1,-1,1,2,-23,-48,212,1037,1928,-222], "decade tables")
    require(all(m * m < n for n, m in enumerate(prefix) if n >= 2),
            "strict historical interval")
    best = 2
    for n in range(3, limit + 1):
        if prefix[n] ** 2 * best > prefix[best] ** 2 * n:
            best = n
    zeros = [n for n in range(1, 429) if prefix[n] == 0]
    levels = {str(j): [n for n in range(1, 349) if prefix[n] == j]
              for j in range(-3, 4)}
    require(best == 5 and 5 * prefix[best] ** 2 == 4 * best, "maximum ratio on the historical range")
    expected_hits = {
        -3: [13, 19, 20, 30, 33, 43, 44, 45, 47, 48, 49, 50],
        -2: [5, 7, 8, 9, 11, 12, 14, 17, 18, 21, 23, 24, 25, 29],
        -1: [3, 4, 6, 10, 15, 16, 22, 26, 27, 28, 35, 36, 38],
        0: [2, 39, 40, 58, 65, 93, 101, 145, 149, 150],
        1: [1, 94, 97, 98, 99, 100, 146, 147, 148, 161],
        2: [95, 96, 217, 229, 335, 336, 339, 340, 345, 347, 348],
        3: [218, 223, 224, 225, 227, 228, 341, 342, 343, 344, 346],
    }
    for level, expected in expected_hits.items():
        require(levels[str(level)][:len(expected)] == expected, "published first level hits")
    require(zeros == [
        2, 39, 40, 58, 65, 93, 101, 145, 149, 150, 159, 160, 163, 164, 166, 214,
        231, 232, 235, 236, 238, 254, 329, 331, 332, 333, 353, 355, 356, 358, 362,
        363, 364, 366, 393, 401, 403, 404, 405, 407, 408, 413, 414, 419, 420, 422,
        423, 424, 425, 427, 428
    ], "published zero list")
    with (directory / "initial-values.csv").open("w", newline="") as out:
        writer = csv.writer(out)
        writer.writerow(("n", "mu", "M"))
        writer.writerows((n, mu[n], prefix[n]) for n in range(1, 429))
    data = {"M_at_powers_of_ten_0_to_9": powers,
            "zeros_through_428": zeros, "levels_through_348": levels,
            "maximum_M_squared_over_n_on_2_to_10000":
                {"first_argmax": best, "M": prefix[best], "numerator": prefix[best] ** 2,
                 "denominator": best},
            "range_crosschecked_by_independent_divisor_inversion": limit,
            "range_crosschecked_by_quotient_algorithm": 512}
    (directory / "finite-checks.json").write_text(json.dumps(data, indent=2) + "\n")
    print("Decade values:", powers)
    print("First maximum of M(n)^2/n, 2 <= n <= 10000:", best, prefix[best], prefix[best]**2)
    print("Zeros through 428:", zeros)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "verification")
    args = parser.parse_args()
    verify(args.output)
