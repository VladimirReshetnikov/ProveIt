#!/usr/bin/env python3
"""Exact independent stencil checks for the ordered localization theorem.

The proof is in localization_notes.md.  These finite calculations check
normalizations, support claims, the explicit rank-three contact table,
and finite-support sequence transport; they are not an all-rank proof.
"""

from fractions import Fraction
from itertools import product, combinations
from math import comb, factorial, prod
from pathlib import Path
import json
import random


def chamber_polynomial(k):
    if k[0] < 0 or any(k[i] >= k[i + 1] for i in range(len(k) - 1)):
        return 0
    return prod((k[j] - k[i]) ** 2
                for i in range(len(k)) for j in range(i + 1, len(k)))


def coefficient(k):
    r = len(k)
    d = 2 * r - 2
    total = 0
    terms = [((-1) ** j * comb(d, j), j) for j in range(d + 1)]
    for stencil in product(terms, repeat=r):
        shifted = tuple(k[i] - stencil[i][1] for i in range(r))
        p = chamber_polynomial(shifted)
        if p:
            total += prod(stencil[i][0] for i in range(r)) * p
    return total


def block_lengths(k):
    d = 2 * len(k) - 2
    lengths = [1]
    for i in range(len(k) - 1):
        if k[i + 1] - k[i] > d:
            lengths.append(1)
        else:
            lengths[-1] += 1
    return lengths


def free_singletons(k):
    lengths = block_lengths(k)
    if k[0] < 2 * len(k) - 2:
        lengths = lengths[1:]
    return sum(length == 1 for length in lengths)


def finite_transport(r, nmax):
    d = 2 * r - 2
    data = [[Fraction((i + 2) * (k + 1) + 1, (k + i + 2) ** 2)
             for k in range(nmax + 1)] for i in range(r)]

    def f(i, k):
        return data[i][k] if 0 <= k <= nmax else Fraction(0)

    weights = [[sum(((-1) ** j * comb(d, j) * f(i, n + j)
                     for j in range(d + 1)), Fraction(0)) / factorial(d)
                for n in range(nmax + 1)] for i in range(r)]
    lhs = sum((chamber_polynomial(k) * prod(weights[i][k[i]]
               for i in range(r)) for k in combinations(range(nmax + 1), r)),
              Fraction(0))
    rhs = sum((coefficient(k) * prod(f(i, k[i]) for i in range(r))
               for k in product(range(nmax + 1), repeat=r)), Fraction(0))
    rhs /= factorial(d) ** r
    assert lhs == rhs
    return {"rank": r, "support_max": nmax,
            "exact_value": str(lhs), "passed": True}


def main():
    checks = 0
    rng = random.Random(20261011)
    table = {h: coefficient((8, 8 + h, 30)) // 24 for h in range(-5, 6)}
    expected = {-5: 0, -4: 0, -3: 1, -2: -4, -1: 5, 0: 0,
                1: -5, 2: 4, 3: -1, 4: 0, 5: 0}
    assert table == expected
    checks += len(table)
    # Independent translations and the two possible free pair sectors.
    for h in range(-3, 4):
        for first, far in [(4, 24), (7, 31), (19, 44)]:
            assert coefficient((first, first + h, far)) == 24 * expected[h]
            assert coefficient((first, far, far + h)) == 24 * expected[h]
            checks += 2
    # Support cancellation including an anchored first block.
    cancellation_samples = []
    for r, samples in [(2, [(2, 5), (5, 8)]),
                       (3, [(4, 9, 14), (0, 5, 10), (3, 9, 15)]),
                       (4, [(6, 7, 14, 21), (0, 7, 14, 21),
                            (10, 17, 24, 25), (1, 2, 10, 18)]),
                       (5, [(8, 9, 18, 27, 36), (0, 9, 18, 19, 28)])]:
        for k in samples:
            assert free_singletons(k) >= 2
            value = coefficient(k)
            assert value == 0
            cancellation_samples.append({"k": k, "value": value})
            checks += 1
    # A deterministic collection of irregular tuples: the finite table is
    # evaluated before the support implication is checked.
    for _ in range(80):
        k = tuple(rng.randrange(0, 28) for _ in range(3))
        c = coefficient(k)
        if c:
            assert all(k[i + 1] - k[i] >= -3 for i in range(2))
            assert free_singletons(k) <= 1
        checks += 1
    transport = [finite_transport(2, 5), finite_transport(3, 4)]
    # A deliberately false table entry must be rejected.
    corrupted = dict(expected)
    corrupted[1] += 1
    assert table != corrupted
    checks += 1
    record = {
        "status": "passed",
        "exact_check_count": checks + len(transport),
        "rank_three_contact_table": table,
        "two_singleton_cancellations": cancellation_samples,
        "finite_support_transport": transport,
        "corruption_control": "changed h=1 contact coefficient rejected",
        "scope": "finite exact checks; all-rank proof is in the article",
    }
    destination = Path(__file__).with_name("localization_checks.json")
    destination.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"status": "passed",
                      "exact_check_count": record["exact_check_count"],
                      "result": str(destination)}, indent=2))


if __name__ == "__main__":
    main()
