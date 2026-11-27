#!/usr/bin/env python3
"""Independent exact finite check of a nonpacking adversary.

No numerical approximations, third-party libraries, or tree dynamic program.
Enumerates all 8008 ten-element subsets of sixteen 2-adic directions.
"""
from itertools import combinations
from math import comb
import json


def v2(n):
    if n == 0:
        raise ValueError("v2(0) is not finite")
    n = abs(n)
    return (n & -n).bit_length() - 1


def p_ordering(points, exponential=True):
    remaining = set(points)
    order, marginals = [], []
    while remaining:
        def cost(x):
            return sum((1 << v2(x-a)) if exponential else v2(x-a)
                       for a in order)
        a = min(remaining, key=lambda x: (cost(x), x))
        marginals.append(cost(a))
        order.append(a)
        remaining.remove(a)
    return order, marginals


def mul_f2(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        b >>= 1
    return result


def branch(b):
    # Coefficients of (1+X)^b - 1 over F2, encoded as bits.
    result = 1
    j = 0
    while b:
        if b & 1:
            result ^= result << (1 << j)
        j += 1
        b >>= 1
    return result ^ 1


def x_order(f):
    return None if f == 0 else (f & -f).bit_length()-1


def main():
    grid = tuple(range(16))
    survivor_count = 10
    extrema = [-1] * survivor_count
    witnesses = [None] * survivor_count
    checked = 0
    for subset in combinations(grid, survivor_count):
        order, values = p_ordering(subset)
        for j, value in enumerate(values):
            if value > extrema[j]:
                extrema[j] = value
                witnesses[j] = {"subset": subset, "order": order,
                                "marginals": values}
        checked += 1
    assert checked == comb(16, 10) == 8008
    assert extrema == [0, 1, 3, 7, 9, 14, 18, 20, 24, 26]
    witness = witnesses[5]
    assert list(witness["subset"]) == [0,1,2,4,5,8,9,10,12,13]

    packed = tuple(range(0, 16, 2)) + (1, 9)
    packed_order, packed_values = p_ordering(packed)
    assert packed_values[5] == 12 < extrema[5] == 14

    roots = [0, 1, 2, 4, 5]
    evaluations, orders = [], []
    for b in grid:
        value = 1
        for a in roots:
            value = mul_f2(value, branch(b) ^ branch(a))
        evaluations.append(value)
        orders.append(x_order(value))
    precision = 14
    mask = (1 << precision) - 1
    residues = [value & mask for value in evaluations]
    support = [b for b, value in enumerate(residues) if value]
    assert support == [3,6,7,11,14,15]
    assert [orders[b] for b in support] == [7,10,7,7,10,7]
    assert all(orders[b] is None or orders[b] >= precision
               for b in witness["subset"])
    # H = product(Y-u_a) is monic in Y of degree5: its <6 jet is nonzero.
    # A received vector halfway between the zero and H observation vectors.
    received = [residues[b] if b in support[:3] else 0 for b in grid]
    distance_from_zero = sum(value != 0 for value in received)
    distance_from_H = sum(x != y for x, y in zip(received, residues))
    assert (distance_from_zero, distance_from_H) == (3, 3)

    record = {
        "arithmetic": "exact integers and F2 polynomial bit vectors",
        "grid": grid, "survivor_count": survivor_count,
        "subsets_enumerated": checked,
        "all_marginal_maxima": extrema,
        "degree5_witness": witness,
        "packed_subset": packed, "packed_order": packed_order,
        "packed_marginals": packed_values,
        "ambiguity": {"precision": precision, "polynomial_branch_roots": roots,
                      "evaluation_X_orders": orders,
                      "nonzero_support": support,
                      "received_bit_polynomials": received,
                      "distance_from_zero": distance_from_zero,
                      "distance_from_H": distance_from_H},
        "conclusion": ("Exhaustive finite factorial bound is14; the sharp general "
                       "recovery theorem therefore gives precision15. Precision14 "
                       "fails by the explicit 3-error ambiguity."),
        "limits": "This script does not formalize the general recovery theorem."
    }
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()

