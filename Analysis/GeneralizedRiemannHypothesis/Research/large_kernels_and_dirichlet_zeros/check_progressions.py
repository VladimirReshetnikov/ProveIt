#!/usr/bin/env python3
"""Exact checks for the progression example modulo 11, using only Python's standard library."""
from fractions import Fraction
from itertools import combinations
from math import gcd

# Coefficients in the basis 1, z, z^2, z^3 of Q(z), z = exp(2 pi i/10).
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)


def times_z(x):
    a, b, c, d = x
    return (-d, a + d, b - d, c + d)


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def times(x, y):
    answer = ZERO
    term = x
    for coefficient in y:
        answer = add(answer, tuple(coefficient * a for a in term))
        term = times_z(term)
    return answer


def power(x, k):
    value = ONE
    for _ in range(k):
        value = times(value, x)
    return value


ROOTS = [ONE]
for _ in range(9):
    ROOTS.append(times_z(ROOTS[-1]))
assert times_z(ROOTS[-1]) == ONE
ELEMENTS = [pow(2, t, 11) for t in range(10)]
assert len(set(ELEMENTS)) == 10


def observed_rank(sample):
    """Rank of the selected Fourier observations expanded into rational rows."""
    pivots = {}
    for t in sample:
        for coord in range(4):
            row = [Fraction(ROOTS[(-t * j) % 10][coord]) for j in range(10)]
            for j in range(10):
                if not row[j]:
                    continue
                if j not in pivots:
                    pivots[j] = [v / row[j] for v in row]
                    break
                coefficient = row[j]
                row = [v - coefficient * b for v, b in zip(row, pivots[j])]
    return len(pivots)


def check_samples():
    order = [10 // gcd(10, t) for t in range(10)]
    degree = {1: 1, 2: 1, 5: 4, 10: 4}
    best = {}
    for n in range(11):
        for sample in combinations(range(10), n):
            orders = {order[t] for t in sample}
            rank = observed_rank(sample)
            assert rank == sum(degree[d] for d in orders)
            if rank < 10:
                continue
            exponents = []
            for d in (5, 10):
                pairs = {min(t, -t % 10) for t in sample if order[t] == d}
                exponents.append(Fraction(degree[d], 2 * len(pairs)) - 1)
            kappa = max(exponents)
            best[n] = min(best.get(n, kappa), kappa)
    assert best == {4: 1, 5: 1, 6: 0, 7: 0, 8: 0, 9: 0, 10: 0}
    print("Exact rational ranks checked for all 1024 subsets.")
    print("Best spacing exponents by size: " + ", ".join(f"{n} -> {e}" for n, e in best.items()))


def fourier(v, t):
    value = ZERO
    for j, m in enumerate(v):
        value = add(value, tuple(m * a for a in ROOTS[(-t * j) % 10]))
    return value


def check_witnesses():
    # Prescribe Fourier coordinates only on the order-five block. Index t=2 is class 4.
    for k in (1, 2, 5, 10, 20):
        block = {t: power(add(ROOTS[t], ROOTS[-t % 10]), k) for t in (2, 4, 6, 8)}
        v = []
        for j in range(10):
            total = ZERO
            for t, alpha in block.items():
                total = add(total, times(alpha, ROOTS[(t * j) % 10]))
            assert total[1:] == (0, 0, 0)
            v.append(total[0])
        for t in range(10):
            assert fourier(v, t) == tuple(10 * a for a in block.get(t, ZERO))
        assert sum(v) == 0
        cap = sum(m for m in v if m > 0)
        print(f"k={k:2d}, each nonnegative vector has mass {cap}, "
              f"normalized difference at class 4 is 10 * golden_ratio^(-{k})")


if __name__ == "__main__":
    check_samples()
    check_witnesses()
