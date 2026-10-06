#!/usr/bin/env python3
"""Reproducible finite checks accompanying Sharper Local Estimates.

The mathematical proofs are in the article. These finite checks look for
normalization, sign, threshold, and rounding errors. Standard library only.
"""
from fractions import Fraction as F
from itertools import product
from math import cos, sin, pi, sqrt, floor


def check_selection():
    cases = 0
    # Direct weighted distributions, including nontrivial threshold atoms.
    for a in (F(1, 5), F(1, 2), F(1)):
        for b in (F(1, 4), F(3, 4), F(1)):
            for fraction in (F(1, 4), F(1, 2), F(3, 4), F(1)):
                moment = fraction * a * b / (a + b)
                max_lower = a * moment / (a - moment)
                for scale in (F(0), F(1, 4), F(3, 4)):
                    t = scale * max_lower
                    p_minus = moment / a
                    p_b = ((a + t) * moment - a * t) / (a * (b - t))
                    p_t = 1 - p_minus - p_b
                    assert min(p_minus, p_t, p_b) >= 0
                    assert -a * p_minus + t * p_t + b * p_b == 0
                    assert t * p_t + b * p_b == moment
                    assert p_b == ((a + t) * moment - a * t) / (a * (b - t))
                    cases += 1
    print(f"Sharp selection: {cases} exact extremizer distributions; PASS")


def check_cubic():
    cases = 0
    for a in (F(1, 100), F(1, 10), F(1, 2), F(1)):
        for j in range(601):
            p = F(j, 200) * a
            left = p ** 3 * (-9 if p < a / 2 else 1)
            right = F(49, 12) * a * a * p - F(343, 108) * a ** 3
            assert left >= right
            cases += 1
        p = F(7, 6) * a
        assert p ** 3 == F(49, 12) * a * a * p - F(343, 108) * a ** 3
    assert F(49, 12) - F(343, 108) == F(49, 54)
    print(f"DRC cubic certificate: {cases} rational points and tangent equalities; PASS")


def phase_partition(n, theta, epsilon):
    length = max(1, floor(sqrt(epsilon * n / (4 * pi))))
    if length == 1:
        return length, [[x] for x in range(n)]
    q_limit = n // length
    distance = lambda q: abs((q * theta + 0.5) % 1 - 0.5)
    step = min(range(1, q_limit + 1), key=distance)
    assert distance(step) <= 1 / (q_limit + 1) + 2e-12
    cells = []
    for residue in range(step):
        chain = list(range(residue, n, step))
        blocks = len(chain) // length
        assert blocks >= 1
        for j in range(blocks - 1):
            cells.append(chain[j * length:(j + 1) * length])
        cells.append(chain[(blocks - 1) * length:])
    return length, cells


def check_phase():
    cases = 0
    for n in (1, 2, 17, 53, 257, 1024):
        for theta in (0.0, 1 / max(n, 1), sqrt(2), 0.3819660112501051):
            for epsilon in (0.01, 0.1, 0.5, 1.0):
                length, cells = phase_partition(n, theta, epsilon)
                assert sorted(x for cell in cells for x in cell) == list(range(n))
                for cell in cells:
                    assert length <= len(cell) <= 2 * length - 1
                    if len(cell) > 1:
                        step = cell[1] - cell[0]
                        assert step > 0
                        assert all(cell[i + 1] - cell[i] == step for i in range(len(cell) - 1))
                    first = cell[0]
                    for x in cell:
                        error = 2 * abs(sin(pi * theta * (x - first)))
                        assert error <= epsilon + 2e-10
                cases += 1
    print(f"Proper phase partitions: {cases} finite cases including singletons; PASS")


def cube_power(f, degree):
    n = len(f)
    total = F(0)
    for params in product(range(n), repeat=degree + 1):
        x, hs = params[0], params[1:]
        value = F(1)
        for vertex in range(1 << degree):
            point = (x + sum(hs[j] for j in range(degree) if vertex >> j & 1)) % n
            value *= f[point]
        total += value
    result = total / n ** (degree + 1)
    assert result >= 0
    return result


def check_progressions():
    cases = 0
    # Count every set directly; norm powers are exact rational averages.
    for n, k in ((5, 3), (5, 4), (7, 3), (7, 4)):
        for mask in range(1 << n):
            indicator = [int(mask >> x & 1) for x in range(n)]
            delta = F(sum(indicator), n)
            f = [F(value) - delta for value in indicator]
            norm_power = cube_power(f, k - 1)
            eta = float(norm_power) ** (1 / (1 << (k - 1)))
            count = sum(all(indicator[(x + j * t) % n] for j in range(k))
                        for x, t in product(range(n), repeat=2))
            factor = sum(float(delta) ** j for j in range(k - 2))
            assert abs(count / (n * n) - float(delta) ** k) <= eta * factor + 1e-12
            nonconstant = count - sum(indicator)
            lower = n * n * (float(delta) ** k - eta * factor) - n * float(delta)
            assert nonconstant >= lower - 1e-10
            cases += 1
    print(f"Progression bounds: all {cases} sets for (N,k)=(5,3),(5,4),(7,3),(7,4); PASS")


if __name__ == "__main__":
    check_selection()
    check_cubic()
    check_phase()
    check_progressions()
    print("All finite estimate checks passed; see the article for proofs.")
