#!/usr/bin/env python3
"""Exact examples for finite section bounds.

This is an implementation and example validator, not a proof checker.
The general theorem is proved in the accompanying human-readable paper.
Only the Python standard library is used.
"""

from fractions import Fraction
from itertools import combinations, permutations
from math import gcd, prod
import json


def trim(p):
    p = [Fraction(a) for a in p]
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    return trim([(p[i] if i < len(p) else 0) +
                 (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def scale(p, a):
    return trim([a * c for c in p])


def mul(p, q):
    if not p or not q:
        return []
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)


def power(p, r):
    out = [Fraction(1)]
    for _ in range(r):
        out = mul(out, p)
    return out


def evaluate(p, x):
    out = Fraction(0)
    for a in reversed(p):
        out = out * x + a
    return out


def synthetic_division(p, z):
    p = trim(p)
    if len(p) <= 1:
        return [], p[0] if p else Fraction(0)
    q = [Fraction(0)] * (len(p) - 1)
    q[-1] = p[-1]
    for i in range(len(p) - 2, 0, -1):
        q[i - 1] = p[i] + z * q[i]
    rem = p[0] + z * q[0]
    assert add(mul([-z, 1], q), [rem]) == p
    return trim(q), rem


def determinant(a):
    n = len(a)
    assert all(len(row) == n for row in a)
    ans = Fraction(0)
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j]
                         for i in range(n) for j in range(i + 1, n))
        ans += (-1) ** inversions * prod(a[i][perm[i]] for i in range(n))
    return ans


def minor(a, rows, cols):
    return [[a[i][j] for j in cols] for i in rows]


def primitive_integer_vector(a):
    d = prod(x.denominator for x in a)
    nums = [int(x * d) for x in a]
    g = 0
    for z in nums:
        g = gcd(g, abs(z))
    assert g > 0
    nums = [z // g for z in nums]
    if next(z for z in reversed(nums) if z != 0) < 0:
        nums = [-z for z in nums]
    return nums


def annihilator(w, n):
    """Bounded exhaustive minor construction from the paper."""
    assert n > 0 and all(len(row) == n for row in w)
    w = [[Fraction(x) for x in row] for row in w]
    den = prod(x.denominator for row in w for x in row)
    v = [[x * den for x in row] for row in w]
    rank, rows, cols = 0, (), ()
    for k in range(1, min(len(v), n) + 1):
        found = None
        for ri in combinations(range(len(v)), k):
            for cj in combinations(range(n), k):
                if determinant(minor(v, ri, cj)) != 0:
                    found = (ri, cj)
                    break
            if found:
                break
        if found:
            rank, rows, cols = k, *found
    if rank == n:
        raise ValueError("The input span is not proper.")
    free = next(j for j in range(n) if j not in cols)
    a = minor(v, rows, cols)
    lam = [Fraction(0)] * n
    lam[free] = determinant(a)
    for i in range(rank):
        for j in range(rank):
            cofactor = (-1) ** (i + j) * determinant(
                minor(a, [h for h in range(rank) if h != j],
                      [h for h in range(rank) if h != i]))
            lam[cols[i]] -= cofactor * v[rows[j]][free]
    lam = primitive_integer_vector(lam)
    assert any(lam)
    assert all(sum(x * y for x, y in zip(row, lam)) == 0 for row in w)
    return lam, rank


def features(x, y, s):
    return [Fraction(x) ** j for j in range(s + 1)] + [Fraction(y)]


def run_examples():
    r, s = 2, 2
    q = [1, 0, 1]
    root_product = [1]
    for j in range(1, 6):
        root_product = mul(root_product, [-j, 1])
    f = add(power(q, 2), root_product)
    pts = [(Fraction(j), evaluate(q, Fraction(j))) for j in range(1, 6)]
    assert all(y ** r == evaluate(f, x) for x, y in pts)
    lam, rank = annihilator([features(x, y, s) for x, y in pts], s + 2)
    p, a = lam[:-1], lam[-1]
    assert a != 0
    h = add(power(scale(p, -1), r), scale(f, -(a ** r)))
    assert len(h) - 1 == 5
    quotient = h
    for x, _ in pts:
        quotient, remainder = synthetic_division(quotient, x)
        assert remainder == 0
    assert len(quotient) == 1 and quotient[0] != 0

    f2 = add([1], mul([0, 0, 0, 1], mul([-1, 1], [-2, 1])))
    pts2 = [(Fraction(x), Fraction(y)) for x in (1, 2) for y in (-1, 1)]
    assert all(y ** r == evaluate(f2, x) for x, y in pts2)
    lam2, rank2 = annihilator([features(x, y, s) for x, y in pts2], s + 2)
    assert lam2[-1] == 0
    assert all(evaluate(lam2[:-1], x) == 0 for x, _ in pts2)
    assert len(set(x for x, _ in pts2)) == 2

    return {
        "status": "Exact examples only; universal claims are proved in the paper.",
        "sharp_quintic": {
            "coefficients_ascending": [int(c) for c in f],
            "points": [[int(x), int(y)] for x, y in pts],
            "rank": rank,
            "annihilator": lam,
            "section_degree": len(h) - 1,
            "successive_division_final_constant": str(quotient[0]),
            "section_bound": 5,
            "attained": len(pts) == 5,
        },
        "zero_y_coefficient_branch": {
            "coefficients_ascending": [int(c) for c in f2],
            "points": [[int(x), int(y)] for x, y in pts2],
            "rank": rank2,
            "annihilator": lam2,
            "x_groups": 2,
            "points_per_x": 2,
            "branch_bound": r * s,
        },
    }


if __name__ == "__main__":
    print(json.dumps(run_examples(), indent=2))
