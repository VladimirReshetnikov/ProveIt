#!/usr/bin/env python3
"""Exact rational checks for the fixed-Gauss aggregate torsion selector.

This verifies finite combinatorics and arithmetic identities, not an analytic
or p-adic formalization. All tested valuation identities use exact fractions.
"""
from fractions import Fraction
from pathlib import Path
import json


def e(p, h):
    return (p - 1) * p ** (h - 1)


def shell_max(p, h, m):
    if m >= e(p, h):
        return None  # +infinity
    return Fraction(sum(e(p, j) * (m // e(p, j)) for j in range(1, h)), e(p, h))


def smallest_blocker(p, h, slack):
    lo, hi = 0, e(p, h)
    while lo < hi:
        m = (lo + hi) // 2
        value = shell_max(p, h, m)
        if value is None or value > slack:
            hi = m
        else:
            lo = m + 1
    return lo


def vp(n, p):
    assert n
    n = abs(n)
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def main():
    greedy_count = 0
    identity_count = 0
    threshold_count = 0
    for p in (2, 3, 5, 7, 11):
        for h0 in range(1, 9):
            c = Fraction(1, p ** (h0 - 1))
            W, root_count = Fraction(0), 0
            for h in range(h0, h0 + 20):
                eh = e(p, h)
                slack = W - Fraction(root_count, eh)
                M = e(p, h - h0 + 1)
                assert shell_max(p, h, M - 1) == slack
                value = shell_max(p, h, M)
                assert value is None or value > slack
                identity_count += 1
                assert smallest_blocker(p, h, slack) == M
                greedy_count += 1
                W += Fraction(M, eh)
                root_count += M
                assert W == (h - h0 + 1) * c
            for n in range(12):
                for delta in (Fraction(0), Fraction(1, 3), Fraction(9, 10)):
                    B = (n + delta) * c
                    H = h0 + int(B / c)
                    assert H == h0 + n
                    assert (H - h0 + 1) * c > B
                    assert (H - h0) * c <= B
                    threshold_count += 1

    construction_count = 0
    point_count = 0
    for p in (2, 3, 5, 7):
        for h0 in range(1, 5):
            W, root_count = Fraction(0), 0
            for h in range(h0, h0 + 4):
                eh = e(p, h)
                if eh > 2500:
                    break
                M = e(p, h - h0 + 1)
                units = [a for a in range(1, p**h) if a % p]
                marked = units[:M]
                marked_set = set(marked)
                slack = W - Fraction(root_count, eh)
                finite_values = []
                for a in units:
                    point_count += 1
                    if a in marked_set:
                        continue  # infinite local valuation
                    excess = sum((Fraction(p**vp(a-b,p)-1, eh) for b in marked), Fraction(0))
                    assert excess > slack
                    finite_values.append(excess)
                theoretical = shell_max(p, h, M)
                if theoretical is None:
                    assert not finite_values
                else:
                    assert min(finite_values) == theoretical
                W += Fraction(M, eh)
                root_count += M
                construction_count += 1

    result = {
        "status": "PASS",
        "arithmetic": "exact Python integers and fractions.Fraction",
        "greedy_shells_checked": greedy_count,
        "sharp_floor_identities_checked": identity_count,
        "boundary_budget_cases_checked": threshold_count,
        "explicit_balanced_shell_constructions_checked": construction_count,
        "primitive_evaluation_points_checked": point_count,
        "scope": "Finite checks support the paper proof; no Lean verification claimed.",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
