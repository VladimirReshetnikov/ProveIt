#!/usr/bin/env python3
"""Exact finite checks for the merged binary/ternary branch argument.

Tests the root, Fourier-indicator and refinement formulas over F_3457,
for both root conventions in the article. This does not verify infinite
branches, arbitrary Hahn supports, class ideals or global choice.
Uses only the Python standard library. Prints JSON; --output also saves it.
"""

import argparse
import json
from math import isqrt
from pathlib import Path


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def prime_factors(n):
    result = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            result.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        result.append(n)
    return result


def verify():
    # Four times the largest common stage divides p-1.
    p = 3457
    generator = 7
    assert is_prime(p)
    assert (p - 1) % (4 * 2**4 * 3**3) == 0
    assert all(pow(generator, (p - 1) // q, p) != 1 for q in prime_factors(p - 1))
    counts = {}

    def check(group, condition):
        if not condition:
            raise AssertionError(group)
        counts[group] = counts.get(group, 0) + 1

    def root(n, j, denominator):
        return pow(generator, ((p - 1) // (denominator * n)) * (1 + denominator * j), p)

    def indicator(n, j, x, denominator):
        ratio = x * pow(root(n, j, denominator), -1, p) % p
        return sum(pow(ratio, power, p) for power in range(n)) * pow(n, -1, p) % p

    # denominator=4 models T^n-i, denominator=2 models T^n+1.
    for denominator in (4, 2):
        for binary_depth in range(5):
            d = 2**binary_depth
            for ternary_depth in range(4):
                t = 3**ternary_depth
                n = d * t
                for k in range(n):
                    x = root(n, k, denominator)
                    binary = pow(x, t, p)
                    ternary = pow(x, d, p)
                    check("compatible_roots", binary == root(d, k % d, denominator)
                          and ternary == root(t, k % t, denominator))
                    for z in range(d):
                        check("binary_indicators", indicator(d, z, binary, denominator)
                              == int(k % d == z))
                    for w in range(t):
                        check("ternary_indicators", indicator(t, w, ternary, denominator)
                              == int(k % t == w))
                for z in range(d):
                    for w in range(t):
                        matches = [k for k in range(n) if k % d == z and k % t == w]
                        check("unique_nonzero_joint_coordinate", len(matches) == 1)
                        x = root(n, matches[0], denominator)
                        check("joint_indicator_value",
                              indicator(d, z, pow(x, t, p), denominator)
                              * indicator(t, w, pow(x, d, p), denominator) % p == 1)
        for depth in range(3):
            t = 3**depth
            for k in range(3 * t):
                x = root(3 * t, k, denominator)
                for j in range(t):
                    check("ternary_refinement", indicator(t, j, pow(x, 3, p), denominator)
                          == sum(indicator(3 * t, j + lift * t, x, denominator)
                                 for lift in range(3)) % p)
    return {
        "status": "passed",
        "field_prime": p,
        "primitive_generator": generator,
        "binary_depths": [0, 4],
        "ternary_depths": [0, 3],
        "counts": counts,
        "total": sum(counts.values()),
        "scope": "Finite-field root formulas, Fourier indicators and coprime refinements only; "
                 "no class ideals or infinite branch proof.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = json.dumps(verify(), indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(report, encoding="utf-8")
    print(report, end="")


if __name__ == "__main__":
    main()
