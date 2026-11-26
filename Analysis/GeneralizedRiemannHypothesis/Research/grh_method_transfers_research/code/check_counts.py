#!/usr/bin/env python3
"""Independently compare basis and unlabeled coset-tree computations."""
from fractions import Fraction as F
from itertools import product
from math import inf
from newton_counts import TorsionBalls
from torsion_window import EllipticExample, obstruction


def check():
    cases = 0
    for high in range(1, 5):
        model = EllipticExample(high)
        group = list(product(range(model.modulus), repeat=2))
        values = sorted({model.valuation(point) for point in group})
        for low in range(1, high + 1):
            rows = []
            for value in values:
                ball = [point for point in group if model.valuation(point) >= value]
                rows.append(['inf' if value == inf else str(value), len(ball),
                             sum(model.order(p) < low for p in ball)])
            tree = TorsionBalls(rows)
            for rho, delta in [(F(1), F(0)), (F(1, 5), F(1, 8))]:
                direct = obstruction(model.window(low), model.valuation, model.distance, rho, delta)
                indirect = obstruction(tree.points, tree.valuation, tree.distance, rho, delta)
                assert direct[:3] == indirect[:3]
                cases += 1
    print(cases, "window, radius, and tolerance combinations agree in both representations.")


if __name__ == '__main__':
    check()
