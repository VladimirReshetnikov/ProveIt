#!/usr/bin/env python3
"""Independent exact ray certificates for two upper-centered candidates.

The global degree upper bounds and factorized homogeneous forms are
proved in centered_degree_proof.tex. This finite exact calculation
supplies independently regenerated lower-bound certificates.
"""
import json
from pathlib import Path


class Poly:
    """Dense univariate integer polynomials, with exact cancellation."""
    def __init__(self, coefficients):
        self.c = list(coefficients)
        while self.c and self.c[-1] == 0:
            self.c.pop()

    def __add__(self, other):
        c = [0] * max(len(self.c), len(other.c))
        for i, a in enumerate(self.c):
            c[i] += a
        for i, a in enumerate(other.c):
            c[i] += a
        return Poly(c)

    def __sub__(self, other):
        return self + Poly([-x for x in other.c])

    def __mul__(self, other):
        if not self.c or not other.c:
            return Poly([])
        c = [0] * (len(self.c) + len(other.c) - 1)
        for i, a in enumerate(self.c):
            if a:
                for j, b in enumerate(other.c):
                    if b:
                        c[i+j] += a*b
        return Poly(c)

    def degree(self):
        return len(self.c) - 1

    def LC(self):
        return self.c[-1] if self.c else 0

    def terms(self):
        return [(i, x) for i, x in enumerate(self.c) if x]

def exact_ray(rows, witnesses):
    env = {x: Poly([0, 1]) for x in witnesses}
    env.update({x: Poly([v])
                for x, v in {'beta': 2, 'K0': 3, 'MC': 5, 'MF': 7}.items()})
    for dst, op, x, y in rows:
        x = env[x] if isinstance(x, str) else Poly([x])
        y = env[y] if isinstance(y, str) else Poly([y])
        env[dst] = x + y if op == '+' else x - y if op == '-' else x * y
    return env['N']

