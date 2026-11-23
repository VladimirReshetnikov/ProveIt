#!/usr/bin/env python3
"""Kauffman bracket by direct resolution of a braid word. Standard library only.

Run with no arguments for finite regression checks, or e.g.
    python jones_states.py 3 1 -2 1 -2
The first argument is strand count. The following signed, one-based generators
are read from top to bottom. The output is the normalized Jones polynomial in A,
where t = A^-4. Each dictionary key is an exponent and its value a coefficient.
"""
from itertools import product
from math import comb
import sys


class Components:
    def __init__(self, size):
        self.parent = list(range(size))

    def find(self, node):
        while self.parent[node] != node:
            self.parent[node] = self.parent[self.parent[node]]
            node = self.parent[node]
        return node

    def join(self, left, right):
        self.parent[self.find(left)] = self.find(right)


def add_term(poly, degree, coefficient):
    value = poly.get(degree, 0) + coefficient
    if value:
        poly[degree] = value
    else:
        poly.pop(degree, None)


def state_expansion(strands, word, closed):
    """For each terminal pairing accumulate its signed Laurent polynomial.

    In closed mode there is only the empty pairing and the state weight uses
    number_of_circles - 1. In open mode only interior circles receive weight.
    """
    if strands < 1 or any(not 1 <= abs(crossing) < strands for crossing in word):
        raise ValueError("braid generators must lie between 1 and strand count minus 1")
    table = {}
    length = len(word)
    final = strands * length
    size = strands * (length + 1)
    for choices in product((0, 1), repeat=length):  # 0 = A and 1 = B
        parts = Components(size)
        for row, (generator, choice) in enumerate(zip(word, choices)):
            left = abs(generator) - 1
            upper = strands * row
            lower = upper + strands
            cap_cup = bool(choice) == (generator > 0)
            for lane in range(strands):
                if not cap_cup or lane not in (left, left + 1):
                    parts.join(upper + lane, lower + lane)
            if cap_cup:
                parts.join(upper + left, upper + left + 1)
                parts.join(lower + left, lower + left + 1)
        if closed:
            for lane in range(strands):
                parts.join(lane, final + lane)
            key = ()
            loops = len({parts.find(n) for n in range(size)}) - 1
        else:
            endpoints = [*range(strands), *range(final, final + strands)]
            boundary = {}
            for index, endpoint in enumerate(endpoints):
                boundary.setdefault(parts.find(endpoint), []).append(index)
            key = tuple(sorted(tuple(pair) for pair in boundary.values()))
            assert all(len(pair) == 2 for pair in key)
            loops = len({parts.find(n) for n in range(size)} - boundary.keys())
        prefactor = length - 2 * sum(choices)
        sign = (-1) ** loops
        polynomial = table.setdefault(key, {})
        for j in range(loops + 1):
            add_term(polynomial, prefactor + 2 * loops - 4 * j, sign * comb(loops, j))
    return {pair: terms for pair, terms in table.items() if terms}


def jones(strands, word):
    writhe = sum(1 if g > 0 else -1 for g in word)
    sign = -1 if writhe % 2 else 1
    bracket = state_expansion(strands, word, closed=True)[()]
    return {degree - 3 * writhe: sign * coefficient for degree, coefficient in bracket.items()}


def checks():
    for n in (2, 3, 4):
        identity = state_expansion(n, [], False)
        for i in range(1, n):
            for first in (i, -i):
                assert state_expansion(n, [first, -first], False) == identity
        for i in range(1, n - 1):
            for sign in (1, -1):
                a, b = sign * i, sign * (i + 1)
                assert state_expansion(n, [a, b, a], False) == state_expansion(n, [b, a, b], False)
    for sign in (1, -1):
        assert jones(2, [sign]) == {0: 1}
    assert jones(1, []) == {0: 1}
    assert jones(2, []) == {-2: -1, 2: -1}
    assert jones(2, [1, 1, 1]) == {-4: 1, -12: 1, -16: -1}
    assert jones(3, [1, -2, 1, -2]) == {8: 1, 4: -1, 0: 1, -4: -1, -8: 1}
    for n in range(1, 12):
        actual = jones(2, [1] * n)
        expected = {2 - 2 * n: (-1) ** (n + 1)}
        for j in range(1, n):
            expected[-2 * n - 2 - 4 * j] = (-1) ** (n + j)
        assert actual == expected
        assert jones(2, [-1] * n) == {-d: value for d, value in actual.items()}
        assert sum(actual.values()) == (1 if n % 2 else -2)
    # Every short three-braid, all orientations taken downward.
    for length in range(5):
        for word in product((1, 2, -1, -2), repeat=length):
            permutation = list(range(3))
            for generator in word:
                lane = abs(generator) - 1
                permutation[lane], permutation[lane + 1] = permutation[lane + 1], permutation[lane]
            components = Components(3)
            for lane, image in enumerate(permutation):
                components.join(lane, image)
            circles = len({components.find(lane) for lane in range(3)})
            value = jones(3, word)
            assert sum(value.values()) == (-2) ** (circles - 1)
            assert all((d - 2 * (circles - 1)) % 4 == 0 for d in value)
    print("Passed open RII/RIII, curl closures, two-braids through 11 crossings,")
    print("figure-eight polynomial, and grading/value at one on 341 three-braids.")


if __name__ == "__main__":
    if len(sys.argv) == 1:
        checks()
    else:
        result = jones(int(sys.argv[1]), tuple(map(int, sys.argv[2:])))
        print(dict(sorted(result.items(), reverse=True)))
