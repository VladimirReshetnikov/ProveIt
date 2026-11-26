#!/usr/bin/env python3
"""Recover the torsion test set from nested subgroup counts and solve its threshold.

Input: a JSON list of [valuation as a string, full subgroup size, excluded
subgroup intersection size], ordered shallow to deep and ending ["inf",1,1].
The first row includes every point, so its valuation is the smallest valuation.
"""
import argparse
from fractions import Fraction
import json
from math import inf
from pathlib import Path
from torsion_window import obstruction


class TorsionBalls:
    def __init__(self, levels):
        self.levels = [(inf if v == "inf" else Fraction(v), g, d) for v, g, d in levels]
        if len(self.levels) < 2 or self.levels[-1] != (inf, 1, 1):
            raise ValueError('the final row must be ["inf", 1, 1]')
        active = [((), True)]
        for (r, g, d), (s, h, e) in zip(self.levels, self.levels[1:]):
            if not (0 < r < s and 1 <= e <= h <= g and e <= d <= g):
                raise ValueError("invalid levels or subgroup counts")
            if g % h or d % e or d // e > g // h:
                raise ValueError("inconsistent subgroup indices")
            children, meeting = g // h, d // e
            active = [(path + (i,), touches and i < meeting)
                      for path, touches in active for i in range(children)]
        self.points = [path for path, excluded in active if not excluded]
        self.origin = (0,) * (len(self.levels) - 1)
        if not self.points:
            raise ValueError("the target set is empty")

    def distance(self, x, y):
        for index, (a, b) in enumerate(zip(x, y)):
            if a != b:
                return self.levels[index][0]
        return inf

    def valuation(self, x):
        return self.distance(x, self.origin)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('counts', type=Path)
    parser.add_argument('--rho', type=Fraction, default=Fraction(1))
    parser.add_argument('--tolerance', type=Fraction, default=Fraction(0))
    args = parser.parse_args()
    tree = TorsionBalls(json.loads(args.counts.read_text()))
    cost, degree, rows, _ = obstruction(tree.points, tree.valuation, tree.distance,
                                       args.rho, args.tolerance)
    print('weight  points  required-excess  minimum-marks')
    for row in rows:
        print('  '.join(map(str, row)))
    print('Minimum budget:', cost, ' Minimum degree:', degree)


if __name__ == '__main__':
    main()
