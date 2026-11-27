#!/usr/bin/env python3
"""Exact finite checks of the symplectic compression results. Run with Python 3.9+.

The reference count enumerates all pairs of rows of one symplectic plane.
Integer convolution then counts the Gram matrix of every rectangular matrix,
including multiplicities, without using a symplectic group order, an orbit
size, a Fourier coefficient, or a closed formula for any probability.
"""
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import prod


def eta(q, n):
    return prod((1 - Fraction(1, q ** (2 * i)) for i in range(1, n + 1)),
                start=Fraction(1))


def matrix_rank(matrix, q):
    matrix = [row[:] for row in matrix]
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[pivot], matrix[rank] = matrix[rank], matrix[pivot]
        pivot_inv = pow(matrix[rank][col], -1, q)
        for i in range(rank + 1, len(matrix)):
            scale = matrix[i][col] * pivot_inv % q
            if scale:
                matrix[i] = [(x - scale * y) % q
                             for x, y in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


class FormSpace:
    def __init__(self, q, b):
        self.q, self.b = q, b
        self.pairs = list(combinations(range(b), 2))
        self.weights = [q ** j for j in range(len(self.pairs))]
        self.size = q ** len(self.pairs)
        self.digits = [tuple(code // w % q for w in self.weights)
                       for code in range(self.size)]
        self.standard = sum(w for w, (i, j) in zip(self.weights, self.pairs)
                            if i % 2 == 0 and j == i + 1)
        self.rank = []
        for digits in self.digits:
            matrix = [[0] * b for _ in range(b)]
            for (i, j), value in zip(self.pairs, digits):
                matrix[i][j], matrix[j][i] = value, -value % q
            self.rank.append(matrix_rank(matrix, q))
        self.additions = {}
        self.plane = self.count_one_plane()
        self.hist = [{0: 1}, self.plane]

    def add(self, x, y):
        if self.q == 2:
            return x ^ y
        return sum(((a + b) % self.q) * w
                   for a, b, w in zip(self.digits[x], self.digits[y], self.weights))

    def residual(self, gram):
        if self.q == 2:
            return self.standard ^ gram
        return sum(((a - b) % self.q) * w for a, b, w
                   in zip(self.digits[self.standard], self.digits[gram], self.weights))

    def count_one_plane(self):
        vectors = list(product(range(self.q), repeat=self.b))
        hist = Counter()
        for x in vectors:
            for y in vectors:
                code = sum(((x[i] * y[j] - x[j] * y[i]) % self.q) * w
                           for w, (i, j) in zip(self.weights, self.pairs))
                hist[code] += 1
        assert sum(hist.values()) == self.q ** (2 * self.b)
        return dict(hist)

    def gram_hist(self, planes):
        while len(self.hist) <= planes:
            values = [0] * self.size
            prev = self.hist[-1]
            for y, mass in self.plane.items():
                if self.q == 2:
                    for x, n in prev.items():
                        values[x ^ y] += mass * n
                else:
                    if y not in self.additions:
                        self.additions[y] = [self.add(x, y) for x in range(self.size)]
                    shifted = self.additions[y]
                    for x, n in prev.items():
                        values[shifted[x]] += mass * n
            counts = {x: v for x, v in enumerate(values) if v}
            assert sum(counts.values()) == self.q ** (2 * self.b * len(self.hist))
            self.hist.append(counts)
        return self.hist[planes]


def check_orbit_transform(space):
    q, b = space.q, space.b
    omega = [i for i, r in enumerate(space.rank) if r == b]
    phase_indices = [space.pairs.index((i, i + 1)) for i in range(0, b, 2)]
    value = Fraction(1)
    for t in range(1, b // 2 + 1):
        phases = Counter(sum(space.digits[x][j] for j in phase_indices[:t]) % q
                         for x in omega)
        # The nonzero additive phases have equal counts, and all their
        # primitive q-th roots of unity sum to -1 for q prime.
        assert all(phases[i] == phases[1] for i in range(1, q))
        value = -value / (q ** (b - 2 * t + 1) - 1)
        assert Fraction(phases[0] - phases[1], len(omega)) == value


def check_case(space, a, complement_dimension):
    q, b = space.q, space.b
    h, c = b // 2, complement_dimension // 2
    n, s = a // 2 + c, c - h
    assert n >= h and a % 2 == complement_dimension % 2 == 0
    visible, hidden = space.gram_hist(a // 2), space.gram_hist(c)
    uniform_count = q ** (a * b)
    # Every counted full matrix has nonsingular specified Gram matrix, so its
    # columns are independent. Witt's extension theorem makes these frames
    # equally likely when a uniform symplectic transformation acts on a frame.
    frame_count = sum(mass * hidden.get(space.residual(x), 0)
                      for x, mass in visible.items())
    assert frame_count > 0
    observed = Counter()
    for x, mass in visible.items():
        observed[b - space.rank[space.residual(x)]] += mass
    differences = sum(mass * abs(hidden.get(space.residual(x), 0) * uniform_count - frame_count)
                      for x, mass in visible.items())
    matrix_tv = Fraction(differences, 2 * uniform_count * frame_count)
    if s >= 0:
        alpha = eta(q, c) * eta(q, n - h) / (eta(q, s) * eta(q, n))
        specified_tv = (1 - alpha) * Fraction(observed[0], uniform_count)
    else:
        specified_tv = Fraction(sum(m for k, m in observed.items() if b - k > 2 * c),
                                uniform_count)
    assert matrix_tv == specified_tv
    for code, rank in enumerate(space.rank):
        weight = hidden.get(code, 0) * uniform_count
        assert (weight > 0) == (rank <= 2 * c)
        favored = (rank < b) if s >= 0 else (rank <= 2 * c)
        assert (weight > frame_count) == favored
        assert weight != frame_count
        if s >= 0 and rank == b:
            assert Fraction(weight, frame_count) == alpha

    uniform_hist = Counter(b - r for r in space.rank)
    theta = Fraction(uniform_hist[0], space.size)
    # The finite positive Fourier sum for the nonsingular residual.
    p_nonsingular = Fraction(0)
    for t in range(h + 1):
        quotient = eta(q, h) / (eta(q, t) * eta(q, h - t))
        theta_short = prod((1 - Fraction(1, q ** (2 * j - 1))
                            for j in range(1, h - t + 1)), start=Fraction(1))
        p_nonsingular += quotient * theta_short / q ** ((a + 1) * t)
    assert p_nonsingular == Fraction(observed[0], uniform_count)
    l1_remainder = Fraction(0)
    for k, mass in uniform_hist.items():
        coeff = Fraction(q ** b - 1 - q ** (b - 1) * (q ** k - 1),
                         (q * q - 1) * (q ** (b - 1) - 1))
        predicted = Fraction(mass, space.size) * (1 + Fraction(1, q ** a) * coeff)
        l1_remainder += abs(Fraction(observed[k], uniform_count) - predicted)
    assert l1_remainder ** 2 <= (1 / theta - 1) / q ** (4 * a)
    return dict(q=q, a=a, b=b, complement=complement_dimension,
                ambient_dimension=2 * n, s=s, frames=str(frame_count),
                full_tv=str(matrix_tv), residual_nonsingular=str(Fraction(observed[0], uniform_count)),
                corank_linearization_l1=str(l1_remainder))


def main():
    # Each pair lists the observed row count and the hidden row count.
    cases = {
        (2, 2): [(2, 0), (2, 2), (4, 4)],
        (2, 4): [(4, 0), (2, 2), (4, 2), (2, 4), (4, 4), (6, 4), (2, 6), (4, 8)],
        (2, 6): [(6, 0), (4, 2), (2, 4), (2, 6), (2, 8)],
        (3, 2): [(2, 0), (2, 2), (4, 4)],
        (3, 4): [(4, 0), (2, 2), (4, 2), (2, 4), (4, 4), (6, 4), (2, 6), (4, 8)],
    }
    results = []
    for (q, b), dimensions in cases.items():
        space = FormSpace(q, b)
        check_orbit_transform(space)
        results.extend(check_case(space, a, hidden) for a, hidden in dimensions)
    print(json.dumps(dict(cases=len(results), status="passed", results=results), indent=2))


if __name__ == "__main__":
    main()
