#!/usr/bin/env python3
"""Exact cyclotomic shell thresholds and independent exhaustive verification.

With no arguments run the exhaustive tests and print a sample table.
With --table P H0 H DELTA, calculate all thresholds and the exact cost.
DELTA accepts rationals such as 1/2. Only the Python standard library is needed.
"""

import argparse
from fractions import Fraction
from itertools import combinations_with_replacement
from math import isqrt


def require_prime(p):
    if p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError("p must be prime")


def shell_size(p, h):
    return (p - 1) * p ** (h - 1)


def loss_numerator(p, h, marks):
    """Finite optimal minimum loss, in units of 1/phi(p^h)."""
    n = shell_size(p, h)
    if not 0 <= marks < n:
        raise ValueError("finite loss requires fewer marks than primitive roots")
    total = 0
    size = p - 1
    for _ in range(1, h):
        total += size * (marks // size)
        size *= p
    return total


def blocking_marks(p, h, tolerance):
    """Least integer marks with loss strictly greater than tolerance."""
    n = shell_size(p, h)
    low, high = 0, n
    while low < high:
        middle = (low + high) // 2
        if loss_numerator(p, h, middle) * tolerance.denominator > n * tolerance.numerator:
            high = middle
        else:
            low = middle + 1
    return low


def direct_cost_units(p, a, b):
    """Loss from the mark b at the distinct unit exponent a, scaled by phi."""
    difference = abs(a - b)
    if difference == 0:
        raise ValueError("evaluation at a marked leaf is infinite")
    power = 1
    while difference % p == 0:
        difference //= p
        power *= p
    return power - 1


def check_shell(p, h):
    units = [a for a in range(1, p**h) if a % p]
    n = len(units)
    assert n == shell_size(p, h)
    # An entry on the diagonal is ignored since that leaf gives infinite loss.
    distances = [[None if a == b else direct_cost_units(p, a, b)
                  for b in units] for a in units]
    total_configurations = 0
    for count in range(n):
        best = 0
        for multiset in combinations_with_replacement(range(n), count):
            loss = min(sum(distances[a][b] for b in multiset)
                       for a in range(n) if a not in multiset)
            best = max(best, loss)
            total_configurations += 1
            if multiset == tuple(range(count)):
                assert loss == loss_numerator(p, h, count)
        assert best == loss_numerator(p, h, count)
    # Compare binary search at equality and between adjacent rational values.
    threshold_units = {loss_numerator(p, h, k) for k in range(n)}
    tests = {Fraction(0), Fraction(1, 2), Fraction(1), Fraction(20)}
    for z in threshold_units:
        tests.add(Fraction(z, n))
        tests.add(Fraction(2 * z + 1, 2 * n))
    for tolerance in tests:
        direct = next((k for k in range(n)
                       if Fraction(loss_numerator(p, h, k), n) > tolerance), n)
        assert direct == blocking_marks(p, h, tolerance)
    return total_configurations


def table(p, h0, hmax, tolerance):
    require_prime(p)
    if h0 < 1 or hmax < h0 or tolerance < 0:
        raise ValueError("require 1 <= H0 <= H and a nonnegative tolerance")
    cumulative = Fraction(0)
    print(f"p={p}, start={h0}, tolerance={tolerance}")
    print("h,primitive_roots,minimum_marks,shell_cost,cumulative_cost")
    for h in range(h0, hmax + 1):
        n = shell_size(p, h)
        k = blocking_marks(p, h, tolerance)
        cost = Fraction(k, n)
        cumulative += cost
        print(f"{h},{n},{k},{cost},{cumulative}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table", nargs=4, metavar=("P", "H0", "H", "DELTA"))
    args = parser.parse_args()
    if args.table:
        p, h0, h, delta = args.table
        table(int(p), int(h0), int(h), Fraction(delta))
        return
    shells = [(2, h) for h in range(1, 5)] + [(3, 1), (3, 2), (5, 1), (7, 1)]
    configurations = sum(check_shell(p, h) for p, h in shells)
    print(f"PASS: {configurations} mark multisets across {len(shells)} shells")
    for p in (2, 3, 5, 7, 11):
        for h in range(1, 40):
            assert blocking_marks(p, h, Fraction(0)) == p - 1
    print("PASS: exact zero-tolerance threshold at 195 prime/height pairs")
    table(2, 1, 14, Fraction(1))


if __name__ == "__main__":
    main()
