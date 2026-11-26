#!/usr/bin/env python3
"""Exact finite-set torsion budgets from valuations. Python 3, standard library."""
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import inf
import argparse


def shell_sequence(points, weight, distance):
    """Greedy Newton sequence. None represents infinite excess at the end."""
    live = {point: F(0) for point in points}
    ordering, excesses = [], []
    while live:
        node = min(live, key=lambda p: (live[p], p))
        excesses.append(live.pop(node))
        ordering.append(node)
        for other in live:
            live[other] += distance(node, other) - weight
    return ordering, excesses + [inf]


def obstruction(points, valuation, distance, rho, tolerance):
    """Return exact cost, degree, shell rows and extremal root list."""
    if rho <= 0 or tolerance < 0 or not points:
        raise ValueError("Require a positive radius parameter, nonnegative loss, and test points")
    shells = {}
    for point in points:
        shells.setdefault(min(valuation(point), rho), []).append(point)
    budget, roots, rows = F(0), [], []
    for weight in sorted(shells, reverse=True):
        threshold = tolerance + budget - len(roots) * weight
        order, sequence = shell_sequence(shells[weight], weight, distance)
        degree = next(i for i, e in enumerate(sequence) if e > threshold)
        roots.extend(order[:degree])
        budget += degree * weight
        rows.append((weight, len(order), threshold, degree))
    return budget, len(roots), rows, roots


def order_exponent(coordinate, level):
    if coordinate == 0:
        return 0
    return level - ((coordinate & -coordinate).bit_length() - 1)


class EllipticExample:
    """Compatible torsion basis on y² + πxy + y = x³, π⁴=2."""
    def __init__(self, level):
        self.level = level
        self.modulus = 2 ** level

    def order(self, point):
        return max(order_exponent(x, self.level) for x in point)

    def valuation(self, point):
        a, b = (order_exponent(x, self.level) for x in point)
        va = (inf if a == 0 else F(3, 4) if a == 1 else F(1, 4 ** (a - 1)))
        vb = inf if b == 0 else F(1, 8 * 4 ** (b - 1))
        return min(va, vb)

    def distance(self, left, right):
        return self.valuation(tuple((a - b) % self.modulus for a, b in zip(left, right)))

    def window(self, low):
        return [point for point in product(range(self.modulus), repeat=2)
                if self.order(point) >= low]


def brute_shell(points, w, distance):
    """Independent minimax by enumeration allowing repeated chosen roots."""
    sequence = []
    for m in range(len(points)):
        best = max(min(sum((distance(x, y) - w for y in roots), F(0)) for x in points)
                   for roots in combinations_with_replacement(points, m))
        sequence.append(best)
    return sequence + [inf]


def residuals(points, roots, valuation, distance, rho):
    return [sum((distance(z, u) - min(valuation(u), rho) for u in roots), F(0))
            for z in points]


def verify():
    example = EllipticExample(2)
    points = example.window(2)
    for r in (F(1), F(1, 5), F(1, 16)):
        for w in sorted({min(example.valuation(x), r) for x in points}):
            shell = [x for x in points if min(example.valuation(x), r) == w]
            if len(shell) <= 8:
                _, seq = shell_sequence(shell, w, example.distance)
                assert seq == brute_shell(shell, w, example.distance)
        for tolerance in (F(0), F(3, 32), F(1, 8), F(1, 2), F(2)):
            budget, degree, rows, roots = obstruction(points, example.valuation,
                                                      example.distance, r, tolerance)
            assert all(v > tolerance for v in
                       residuals(points, roots, example.valuation, example.distance, r))
            assert sum(m for _, _, _, m in rows) == degree
            assert sum(m * w for w, _, _, m in rows) == budget
    for n in range(2, 6):
        group = EllipticExample(n)
        budget, degree, _, _ = obstruction(group.window(n), group.valuation,
                                            group.distance, F(1), F(0))
        assert (budget, degree) == (F(15, 32 * 4 ** (n - 2)), 5)
    print("Exact shell minimax (including repeated marks), clipped radii,")
    print("five tolerances, extremal evaluations, and levels 2 through 5 passed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--low', type=int, default=2)
    parser.add_argument('--high', type=int, default=2)
    parser.add_argument('--rho', type=F, default=F(1))
    parser.add_argument('--tolerance', type=F, default=F(0))
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    if args.verify:
        verify()
    if not 1 <= args.low <= args.high:
        parser.error("require 1 <= low <= high")
    group = EllipticExample(args.high)
    points = group.window(args.low)
    budget, degree, rows, roots = obstruction(points, group.valuation, group.distance,
                                             args.rho, args.tolerance)
    print("weight  points  required-excess  minimum-marks")
    for row in rows:
        print("  ".join(map(str, row)))
    print("Minimum budget:", budget, " Minimum degree:", degree)
    print("Root coordinates modulo", group.modulus, ":", roots)


if __name__ == '__main__':
    main()
