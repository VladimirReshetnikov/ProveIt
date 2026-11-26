#!/usr/bin/env python3
"""Exhaust cyclotomic layouts on small shells; print formula costs on larger ones.

Layouts contain m primitive exponents, with repetitions allowed. Scores use
valuation units 1/e_h until hits, whose score is infinite. A layout's score
is the minimum over all evaluation points. The minimax value maximizes it.
"""
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb, inf


def phi_power(p, h):
    return (p - 1) * p ** (h - 1)


def formula_units(p, h, m):
    """Predicted maximal minimum excess, scaled by e_h."""
    if m >= phi_power(p, h):
        return inf
    return sum(e * (m // e) for e in (phi_power(p, j) for j in range(1, h)))


def point_score(p, a, b):
    """Actual valuation of the root difference, less baseline and scaled by e_h."""
    if a == b:
        return inf
    k, diff = 1, abs(a - b)
    while diff % p == 0:
        k *= p
        diff //= p
    return k - 1


def check_shell(p, h):
    q = p ** h
    units = [a for a in range(1, q) if a % p]
    e = len(units)
    scores = [[point_score(p, a, b) for b in units] for a in units]

    def score(layout):
        return min(sum(scores[i][j] for i in layout) for j in range(e))

    count = 0
    for m in range(e + 1):
        target = formula_units(p, h, m)
        best = -1
        for layout in combinations_with_replacement(range(e), m):
            best = max(best, score(layout))
            count += 1
        assert best == target, (p, h, m, best, target)
        assert score(range(m)) == best, (p, h, m, "ordered prefix")
    assert count == comb(2 * e, e)
    return count


def least_blocking_m(p, h, eps):
    e = phi_power(p, h)
    left, right = 0, e
    while left < right:
        mid = (left + right) // 2
        if formula_units(p, h, mid) > e * eps:
            right = mid
        else:
            left = mid + 1
    assert left and formula_units(p, h, left - 1) <= e * eps
    assert formula_units(p, h, left) > e * eps
    return left


def main():
    counts = []
    for p in (2, 3, 5, 7):
        h = 1
        while phi_power(p, h) <= 8:
            count = check_shell(p, h)
            counts.append(count)
            print(f"p={p} h={h} e={phi_power(p,h)} layouts={count} OK")
            h += 1
    print(f"Total: {sum(counts)} layouts in {len(counts)} shells.")
    eps = Fraction(1, 8)
    print(f"Strictly blocking each shell at epsilon={eps}:")
    print("p,h,m,minimal_shell_cost,cumulative_cost")
    for p in (2, 3, 5):
        total = Fraction()
        for h in range(1, 17):
            e = phi_power(p, h)
            m = least_blocking_m(p, h, eps)
            cost = Fraction(m, e)
            total += cost
            print(f"{p},{h},{m},{cost},{total}")


if __name__ == "__main__":
    main()
