#!/usr/bin/env python3
"""Exact, standard-library checks of nonseparable weighted distributions.

All ranks are over F_2.  The raw relation calculation uses the original
point/monomial presentation and does not call the Koszul routine.  The
Koszul calculation is a separate check of the proof's small examples.
"""

from itertools import combinations, product
from math import comb, gcd
import json


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return len(pivots)


def prime_factors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def monomial_data(lengths):
    monomials = tuple(product(*(range(n) for n in lengths)))
    return monomials, {m: i for i, m in enumerate(monomials)}


def multiply_monomial(x, f, lengths):
    """Return surviving terms of x*f; f is a tuple of monomials."""
    for a in f:
        y = tuple(u + v for u, v in zip(x, a))
        if all(u < n for u, n in zip(y, lengths)):
            yield y


def koszul_homology(lengths, sequence):
    monomials, index = monomial_data(lengths)
    size, r = len(monomials), len(sequence)
    ranks = [0]
    for degree in range(1, r + 1):
        domain = tuple(combinations(range(r), degree))
        target = tuple(combinations(range(r), degree - 1))
        target_index = {x: i for i, x in enumerate(target)}
        columns = []
        for wedge in domain:
            for monomial in monomials:
                column = 0
                for i in wedge:
                    rem = tuple(j for j in wedge if j != i)
                    for y in multiply_monomial(monomial, sequence[i], lengths):
                        column ^= 1 << (target_index[rem] * size + index[y])
                columns.append(column)
        ranks.append(binary_rank(columns))
    ranks.append(0)
    homology = [comb(r, j) * size - ranks[j] - ranks[j + 1]
                for j in range(r + 1)]
    return {"differential_ranks": ranks[1:-1], "homology": homology}


def raw_distribution_dimension(q, lengths, weights, reflect):
    """Expand sum_{py=x} e_y - a_p e_x, and optionally e_{-x}-e_x."""
    monomials, index = monomial_data(lengths)
    size = len(monomials)
    rows = []
    for p in prime_factors(q):
        for target in range(0, q, p):
            sources = tuple(y for y in range(q) if p * y % q == target)
            assert len(sources) == p
            for monomial in monomials:
                row = 0
                for y in sources:
                    row ^= 1 << (y * size + index[monomial])
                for y in multiply_monomial(monomial, weights[p], lengths):
                    row ^= 1 << (target * size + index[y])
                rows.append(row)
    if reflect:
        for a in range(q):
            for i in range(size):
                rows.append((1 << (a * size + i)) ^
                            (1 << ((-a % q) * size + i)))
    rank = binary_rank(rows)
    return {"generators": q * size, "relation_rank": rank,
            "quotient_dimension": q * size - rank}


def run():
    cases = [
        {"name": "two_generator_mixed", "q": 15, "lengths": (3, 3),
         "sequence": (((2, 0),), ((1, 1),)),
         "weights": {3: ((0, 0), (2, 0)), 5: ((0, 0), (1, 1))},
         "expected_homology": [4, 8, 4], "expected_reflected": 44},
        {"name": "three_generator_obstruction", "q": 105,
         "lengths": (2, 2, 2),
         "sequence": (((1, 1, 0),), ((1, 0, 1),), ((0, 1, 1),)),
         "weights": {3: ((0, 0, 0), (1, 1, 0)),
                     5: ((0, 0, 0), (1, 0, 1)),
                     7: ((0, 0, 0), (0, 1, 1))},
         "expected_homology": [4, 14, 14, 4], "expected_reflected": 210},
        {"name": "redundant_third_active_parameter", "q": 105,
         "lengths": (3, 3),
         "sequence": (((2, 0),), ((1, 1),), ((2, 1), (1, 2))),
         "weights": {3: ((0, 0), (2, 0)), 5: ((0, 0), (1, 1)),
                     7: ((0, 0), (2, 1), (1, 2))},
         "expected_homology": [4, 12, 12, 4], "expected_reflected": 232},
    ]
    results = []
    for case in cases:
        q, lengths = case["q"], case["lengths"]
        homology = koszul_homology(lengths, case["sequence"])
        raw = raw_distribution_dimension(q, lengths, case["weights"], True)
        unreflected = raw_distribution_dimension(q, lengths, case["weights"], False)
        size = len(monomial_data(lengths)[0])
        phi = sum(gcd(i, q) == 1 for i in range(q))
        assert homology["homology"] == case["expected_homology"]
        assert raw["quotient_dimension"] == case["expected_reflected"]
        assert unreflected["quotient_dimension"] == size * phi
        assert raw["quotient_dimension"] == (
            size * phi + sum(homology["homology"])) // 2
        # Corruption control: reflection is essential in every case.
        assert unreflected["quotient_dimension"] != raw["quotient_dimension"]
        results.append({"name": case["name"], "q": q, "lengths": lengths,
                        **homology, "raw_reflected": raw,
                        "raw_unreflected": unreflected})
    return {"arithmetic": "exact F_2 bit elimination",
            "status": "all assertions passed", "cases": results}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
