#!/usr/bin/env python3
"""Exact finite checks for the analysis framework.

These examples exercise the displayed rational constructions. They are not
substitutes for the general proofs or for object-language iPRA derivations.
Only Python's standard library is used.
"""

from fractions import Fraction as Q
from itertools import combinations
import json


def dyadic(k):
    return Q(1, 2 ** k)


def objective(x):
    return (x - Q(1, 3)) ** 2


def finite_minimum(k):
    # On [0,1], |objective(x)-objective(y)| <= 2|x-y|.
    # mu(j)=j+1; the theorem uses grid exponent mu(k+2)=k+3.
    exponent = k + 3
    denominator = 2 ** exponent
    grid = [Q(j, denominator) for j in range(denominator + 1)]
    index = min(range(len(grid)), key=lambda j: (objective(grid[j]), j))
    point = grid[index]
    sample_min = objective(point)  # exact evaluation is a valid sampler
    return {
        "k": k,
        "point": point,
        "sample_min": sample_min,
        "lower": sample_min - dyadic(k) / 2,
        "upper": sample_min + dyadic(k) / 4,
        "evaluations": len(grid),
    }


def check_extrema():
    rows = [finite_minimum(k) for k in range(9)]
    current_lower, current_upper = rows[0]["lower"], rows[0]["upper"]
    for row in rows:
        current_lower = max(current_lower, row["lower"])
        current_upper = min(current_upper, row["upper"])
        assert current_lower <= 0 <= current_upper
        assert current_upper - current_lower <= Q(3, 4) * dyadic(row["k"])
        assert row["sample_min"] <= Q(3, 4) * dyadic(row["k"])
    for first in rows:
        for second in rows:
            assert first["lower"] <= second["upper"]
    # lambda=2, c=2, lambda*2^c=8; output precision k uses a_(2k+c).
    points = [rows[2 * k + 2]["point"] for k in range(4)]
    for i in range(len(points)):
        for j in range(len(points)):
            assert abs(points[i] - points[j]) <= dyadic(min(i, j))
    return {
        "precisions": len(rows),
        "grid_evaluations": sum(row["evaluations"] for row in rows),
        "interval_cross_checks": len(rows) ** 2,
        "strong_convex_point_checks": len(points) ** 2,
        "point_samples": [str(x) for x in points],
    }


def verify_binary_amgm(values):
    """Return product, mean and number of checked binary nodes."""
    n = len(values)
    assert n > 0 and n & (n - 1) == 0
    if n == 1:
        assert values[0] > 0
        return values[0], values[0], 0
    left_product, left_mean, left_nodes = verify_binary_amgm(values[: n // 2])
    right_product, right_mean, right_nodes = verify_binary_amgm(values[n // 2 :])
    mean = (left_mean + right_mean) / 2
    product = left_product * right_product
    assert left_mean * right_mean <= mean ** 2
    assert product <= (left_mean * right_mean) ** (n // 2)
    assert product <= mean ** n
    return product, mean, left_nodes + right_nodes + 1


def check_amgm():
    leaves = nodes = 0
    for n in range(1, 66):
        values = [Q((j * j + 3 * j + 5) % 29 + 1, j + 2) for j in range(n)]
        original_mean = sum(values, Q(0)) / n
        m = 1
        while m < n:  # at most n iterations, and m <= 2n
            m *= 2
        padded = values + [original_mean] * (m - n)
        product, mean, checked = verify_binary_amgm(padded)
        assert mean == original_mean and m <= 2 * n
        original_product = Q(1)
        for value in values:
            original_product *= value
        assert product == original_product * mean ** (m - n)
        assert original_product <= mean ** n
        leaves += m
        nodes += checked
    return {"input_lengths": 65, "padded_leaves": leaves, "binary_nodes": nodes}


def check_local_modulus():
    # F(x)=1/x is a positive convex, multiplicatively convex rational example.
    alpha, beta = Q(1, 2), Q(3)
    a, b = alpha / 2, beta + 1
    delta = min(alpha / 2, Q(1))
    bound = Q(5)  # F(a)=4 and F(b)=1/4, so the coarse bound is valid.
    constant = bound / delta
    h = (constant.numerator + constant.denominator - 1) // constant.denominator
    assert constant <= h <= 2 ** h
    samples = [alpha + (beta - alpha) * Q(j, 80) for j in range(81)]
    count = 0
    for x, y in combinations(samples, 2):
        assert abs(1 / x - 1 / y) <= constant * abs(x - y)
        count += 1
    return {"rational_pairs": count, "lipschitz_bound": str(constant), "modulus_offset": h}


def check_metastability():
    controls = [lambda n: n, lambda n: n + 5, lambda n: 2 * n + 3]
    cases = 0
    for g in controls:
        first = (0, g(0))
        second = (g(0) + 1, g(g(0) + 1))
        for jump in [None] + list(range(100)):
            def value(n):
                return int(jump is not None and n >= jump)
            def stable(window):
                l, r = window
                return all(value(i) == value(l) for i in range(l, r + 1))
            chosen = first if stable(first) else second
            assert stable(chosen)
            cases += 1
    return {"one_jump_sequences_and_controls": cases}


if __name__ == "__main__":
    print(json.dumps({
        "status": "all exact finite checks passed",
        "scope": "examples only; not an iPRA proof checker",
        "extrema": check_extrema(),
        "amgm_padding": check_amgm(),
        "local_modulus": check_local_modulus(),
        "metastability": check_metastability(),
    }, indent=2))
