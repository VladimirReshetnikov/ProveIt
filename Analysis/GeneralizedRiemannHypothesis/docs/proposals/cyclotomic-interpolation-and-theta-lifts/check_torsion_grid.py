#!/usr/bin/env python3
"""Exact finite checks for the cyclotomic interpolation argument (standard Python)."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, inf


def ord_p(n, p):
    if n == 0:
        return inf
    value = 0
    while n % p == 0:
        n //= p
        value += 1
    return value


def transversal(p, d, n):
    """Exponents of selected roots relative to a primitive p^(d+n)-th root."""
    return [p**n, *range(1, p**n)]


def radius(p, h):
    return Q(1, (p - 1) * p**(h - 1))


def separation(p, h, exponent):
    """v(xi^exponent - 1) for xi of exact order p^h."""
    if exponent % (p**h) == 0:
        return inf
    return radius(p, h - ord_p(exponent, p))


def check_grid(p, d, n):
    h = d + n
    grid = transversal(p, d, n)
    total = sum(separation(p, h, k) for k in grid)
    assert total == radius(p, d) + Q(n, p**d)
    for i, a in enumerate(grid):
        ra = separation(p, h, a)
        derivative = 0
        for j, b in enumerate(grid):
            if i != j:
                dist = separation(p, h, a - b)
                assert dist == separation(p, n, i - j) / p**d
                derivative += dist
        assert derivative == Q(n, p**d)
        assert total - ra - derivative == radius(p, d) - ra >= 0
    return len(grid)


class Cyclotomic:
    """Integer sums of powers of xi in Q_p(xi), xi primitive of order p^h."""

    def __init__(self, p, h):
        self.p = p
        self.h = h
        self.order = p**h
        self.step = self.order // p
        self.degree = self.order - self.step

    def multiply(self, a, b):
        c = {}
        for i, x in a.items():
            for j, y in b.items():
                e = (i + j) % self.order
                c[e] = c.get(e, 0) + x * y
        return c

    @lru_cache(None)
    def shift_power(self, node, power):
        """The power (xi^node - 1)^power in the cyclic group ring."""
        c = {}
        for j in range(power + 1):
            e = node * j % self.order
            c[e] = c.get(e, 0) + (-1)**(power-j) * comb(power, j)
        return c

    def evaluate(self, polynomial, point):
        c = {}
        for exponents, coeff in polynomial.items():
            term = coeff
            for node, k in zip(point, exponents, strict=True):
                term = self.multiply(term, self.shift_power(node, k))
            for e, a in term.items():
                c[e] = c.get(e, 0) + a
        return c

    def valuation(self, c):
        # Reduce modulo Phi_{p^h}, then expand xi^e = (1 + pi)^e.
        # In the power basis of the uniformizer pi, the finite term valuations
        # are distinct modulo one. Their minimum is the exact valuation.
        coeffs = [c.get(e, 0) - c.get(self.degree + e % self.step, 0)
                  for e in range(self.degree)]
        terms = [(e, a) for e, a in enumerate(coeffs) if a]
        best = inf
        for j in range(self.degree):
            if Q(j, self.degree) >= best:
                break
            a = sum(value * comb(e, j) for e, value in terms if e >= j)
            if a:
                best = min(best, ord_p(a, self.p) + Q(j, self.degree))
        return best

    def gauss(self, polynomial, r):
        return min(self.valuation(coeff) + sum(exponents) * r
                   for exponents, coeff in polynomial.items())


def check_tensor_examples():
    p, d, n = 3, 1, 2
    field = Cyclotomic(p, d + n)
    nodes = transversal(p, d, n)
    points = list(product(nodes, repeat=2))
    one = {0: 1}
    # f = X - (xi^a - 1) has a zero at an actual grid coordinate.
    f = {(1, 0): one, (0, 0): {0: 1, nodes[0]: -1}}
    g = {(0, 1): one, (1, 0): {0: -1}}
    # This example has mixed terms and degree bigger than the grid size.
    k = {(0, 0): {0: 3}, (1, 1): one, (12, 5): {1: 1, 0: -1}}
    # The endpoint radius belongs to a real node and requires no strict slack.
    r = radius(p, d)
    for poly in (f, g, k):
        assert field.gauss(poly, r) < r + Q(n, p**d)
        assert min(field.valuation(field.evaluate(poly, pt)) for pt in points
                   ) <= field.gauss(poly, r)
    # Apply the tensor lemma to the product of two tests at once. Additivity of
    # the Gauss valuation gives a budget strictly below the node-polynomial cost.
    pair_budget = field.gauss(f, r) + field.gauss(g, r)
    assert pair_budget < r + Q(n, p**d)
    pair_minimum = min(sum(field.valuation(field.evaluate(poly, pt)) for poly in (f, g))
                       for pt in points)
    assert pair_minimum <= pair_budget
    thresholds = [field.gauss(poly, r) for poly in (f, g, k)]
    good = [pt for pt in points if all(field.valuation(field.evaluate(poly, pt)) <= t
                                      for poly, t in zip((f, g, k), thresholds))]
    assert good and len(good) < len(points)
    print(f"Tensor checks: {len(points)} grid points, three mixed/ramified tests,"
          f" {len(good)} common witnesses in this example.")


def check_bands():
    # The middle test forces use of the second band; the other two use the first.
    p, B, delta = 2, Q(3, 4), Q(2, 5)
    endpoints = [1]
    for _ in range(int(B // delta) + 1):
        d = endpoints[-1]
        endpoints.append(d + int(B * p**d) + 1)
    assert endpoints == [1, 3, 10]
    h = endpoints[-1]
    field = Cyclotomic(p, h)
    pi4 = {2**(h-2): 1, 0: -1}   # valuation 1/2
    pi8 = {2**(h-3): 1, 0: -1}   # valuation 1/4
    examples = [
        {(8,): {0: 1}, (0,): pi4},
        {(1,): {0: 1}, (0,): field.multiply(pi4, pi8)},
        {(1,): {0: 1}, (0,): pi8},
    ]
    bands_used = []
    for poly in examples:
        ws = [field.gauss(poly, radius(p, d)) for d in endpoints]
        assert ws[0] <= B
        j = next(j for j in range(len(ws)-1) if ws[j]-ws[j+1] <= delta)
        bands_used.append(j+1)
        d, end = endpoints[j:j+2]
        reps = [k*2**(h-end) for k in transversal(p, d, end-d)]
        assert any(field.valuation(field.evaluate(poly, (k,))) <= ws[j] for k in reps)
        assert any(field.valuation(field.evaluate(poly, (k,)))
                   <= field.gauss(poly, separation(p, h, k))+delta for k in reps)
    assert bands_used == [1, 2, 1]
    print(f"Band checks: endpoints {endpoints}, selected bands {bands_used}.")


if __name__ == "__main__":
    cases = [(p,d,n) for p in (2,3,5) for d in (1,2,3) for n in (1,2,3)]
    nodes = sum(check_grid(*case) for case in cases)
    print(f"Metric checks: {len(cases)} grids, {nodes} selected roots; all pair identities verified.")
    check_tensor_examples()
    check_bands()
