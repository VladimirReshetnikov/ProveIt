#!/usr/bin/env python3
"""Exact combinatorial checks for the fixed-radius specialization proof.

Run with Python 3.10 or later. No third-party libraries or network required.
Finite checks do not replace the theorem's proof for arbitrary polynomials.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement, product
from math import inf


def degree(p, h):
    return (p - 1) * p ** (h - 1)


def formula(p, h, m):
    e = degree(p, h)
    if m >= e:
        return inf
    return Q(sum(degree(p, j) * (m // degree(p, j))
                 for j in range(1, h)), e)


def leaf_distances(p, h):
    """Entry (a,b) gives e_h times the excess of a single root at b."""
    units = [a for a in range(1, p ** h) if a % p]
    matrix = []
    for a in units:
        row = []
        for b in units:
            if a == b:
                row.append(inf)
            else:
                power = 1
                while (a - b) % (power * p) == 0:
                    power *= p
                row.append(power - 1)
        matrix.append(row)
    return matrix


def direct_scores(p, h):
    """Try every multiset of m marks for 0 <= m < e_h."""
    matrix = leaf_distances(p, h)
    e = len(matrix)
    scores = []
    for m in range(e):
        best = max(min(sum(row[b] for b in marks) for row in matrix)
                   for marks in combinations_with_replacement(range(e), m))
        scores.append(Q(best, e))
    return scores + [inf]


def recurrence(p, shells, delta):
    e = [degree(p, h) for h in shells]
    counts = []
    for i, h in enumerate(shells):
        savings = sum(m * (Q(1, e[j]) - Q(1, e[i]))
                      for j, m in enumerate(counts))
        counts.append(next(m for m in range(e[i] + 1)
                           if formula(p, h, m) > delta + savings))
    return counts


def whole_grid_minimum(p, shells, delta, scores):
    """All count vectors, using independently enumerated leaf optima."""
    e = [degree(p, h) for h in shells]
    feasible = []
    for counts in product(*(range(n + 1) for n in e)):
        cost = sum(Q(m, n) for m, n in zip(counts, e))
        for i, h in enumerate(shells):
            gauss_at_h = sum(m * min(Q(1, n), Q(1, e[i]))
                             for m, n in zip(counts, e))
            if gauss_at_h + scores[p, h][counts[i]] <= cost + delta:
                break
        else:
            feasible.append(cost)
    return min(feasible)


def main():
    direct = {}
    for p, h in [(2, 1), (2, 2), (2, 3), (2, 4),
                 (3, 1), (3, 2), (5, 1), (7, 1)]:
        direct[p, h] = direct_scores(p, h)
        assert direct[p, h] == [formula(p, h, m)
                                 for m in range(degree(p, h) + 1)]
    print("Single-shell minimax: every multiset checked on 8 small shells.")

    families = [(2, [1, 2, 3]), (2, [2, 3]), (2, [2, 4]),
                (2, [1, 3, 4]), (3, [1, 2]), (3, [2]), (5, [1])]
    for p, shells in families:
        for delta in [Q(0), Q(1, 4), Q(1, 2), Q(1), Q(5, 4)]:
            counts = recurrence(p, shells, delta)
            value = sum(Q(m, degree(p, h)) for m, h in zip(counts, shells))
            assert value == whole_grid_minimum(p, shells, delta, direct)
    print("Finite-grid optimum: 35 independent count-vector searches passed.")

    cases = 0
    for p in [2, 3, 5, 7, 11]:
        for h0 in range(1, 6):
            for k in range(1, 12):
                h = h0 + k - 1
                e, m = degree(p, h), degree(p, k)
                reference = sum(degree(p, j - h0 + 1) *
                                (Q(1, degree(p, j)) - Q(1, e))
                                for j in range(h0, h))
                assert formula(p, h, m - 1) == reference < formula(p, h, m)
                assert Q(m, e) == Q(1, p ** (h0 - 1))
                cases += 1
    print(f"Closed form: both endpoint inequalities passed in {cases} cases.")

    p, shells = 3, [2, 3, 4]
    counts = recurrence(p, shells, Q(0))
    assert counts == [2, 6, 18]
    print("Example p=3, h0=2, B=1: counts 2, 6, 18; cost 1; first guaranteed h=5.")


if __name__ == "__main__":
    main()
