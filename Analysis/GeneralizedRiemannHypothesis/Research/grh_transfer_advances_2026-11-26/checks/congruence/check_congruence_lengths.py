#!/usr/bin/env python3
"""Exact small certificates for the congruence-length diagnostic.

Python standard library only. Integer Smith factors are recovered from gcds of
all minors, independently of any symbolic-algebra package. Modular kernels are
then enumerated on small cases. These are abstract linear-algebra examples,
not certificates of arithmetic Galois representation hypotheses.
"""
from itertools import combinations, product
from math import gcd
from functools import reduce
from pathlib import Path
import json


def determinant(a):
    """Fraction-free Bareiss determinant, with exact divisions."""
    a = [list(row) for row in a]
    n = len(a)
    if n == 0:
        return 1
    sign, previous = 1, 1
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        p = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * p - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = p
    return sign * a[-1][-1]


def smith_from_minors(a):
    rows, cols = len(a), len(a[0])
    divisors, previous = [], 1
    for k in range(1, min(rows, cols) + 1):
        minors = (
            abs(determinant([[a[i][j] for j in cc] for i in rr]))
            for rr in combinations(range(rows), k)
            for cc in combinations(range(cols), k)
        )
        delta = reduce(gcd, minors, 0)
        if not delta:
            break
        assert delta % previous == 0
        divisors.append(delta // previous)
        previous = delta
    assert all(y % x == 0 for x, y in zip(divisors, divisors[1:]))
    return divisors, cols - len(divisors)


def valuation(a, p):
    assert a != 0
    a, v = abs(a), 0
    while a % p == 0:
        a //= p
        v += 1
    return v


def length(exponents, free_rank, k):
    return free_rank * k + sum(min(k, a) for a in exponents)


def kernel_count(a, p, k):
    modulus = p**k
    return sum(
        all(sum(row[j] * x[j] for j in range(len(x))) % modulus == 0 for row in a)
        for x in product(range(modulus), repeat=len(a[0]))
    )


def pairing_matrix(diagonal_a, diagonal_c, chi, symmetry="all"):
    """Rows of A^t B C - chi B for diagonal A and C."""
    n = len(diagonal_a)
    basis = []
    indices = product(range(n), repeat=2) if symmetry == "all" else combinations(range(n), 2)
    if symmetry == "symmetric":
        indices = [(i, j) for i in range(n) for j in range(i, n)]
    for i, j in indices:
        b = [[0] * n for _ in range(n)]
        b[i][j] = 1
        if symmetry != "all" and i != j:
            b[j][i] = 1 if symmetry == "symmetric" else -1
        basis.append(b)
    return [
        [(diagonal_a[i] * diagonal_c[j] - chi) * b[i][j] for b in basis]
        for i in range(n) for j in range(n)
    ]


def run_case(name, a, p, expected_free, expected_exponents, brute_levels=(1,)):
    factors, free = smith_from_minors(a)
    exponents = [valuation(x, p) for x in factors]
    assert free == expected_free, (name, free)
    assert exponents == expected_exponents, (name, exponents)
    brute = []
    for k in brute_levels:
        observed = kernel_count(a, p, k)
        predicted = p**length(exponents, free, k)
        assert observed == predicted, (name, k, observed, predicted)
        brute.append({"k": k, "observed_kernel_order": observed,
                      "predicted_kernel_order": predicted})
    return {"name": name, "prime": p, "relation_matrix": a,
            "integer_smith_factors": factors, "pi_exponents": exponents,
            "rational_hom_dimension": free,
            "lengths_k_1_through_6": [length(exponents, free, k) for k in range(1, 7)],
            "supremum": "infinite" if free else sum(exponents),
            "brute_force_checks": brute}


def main():
    cases = [
        run_case("rank_one_congruent_distinct", [[125]], 5, 0, [3], (1, 2, 3, 4)),
        run_case("rank_one_identical", [[0]], 5, 1, [], (1, 2, 3)),
        run_case("pairing_finite_full", pairing_matrix([1, 26], [1, 26], 126),
                 5, 0, [2, 2, 2, 3]),
        run_case("pairing_finite_symmetric", pairing_matrix([1, 26], [1, 26], 126, "symmetric"),
                 5, 0, [2, 2, 3]),
        run_case("pairing_finite_alternating", pairing_matrix([1, 26], [1, 26], 126, "alternating"),
                 5, 0, [2], (1, 2, 3)),
        run_case("pairing_selfdual_full", pairing_matrix([1, 26], [1, 26], 26),
                 5, 2, [2, 2]),
        run_case("pairing_selfdual_symmetric", pairing_matrix([1, 26], [1, 26], 26, "symmetric"),
                 5, 1, [2, 2]),
        run_case("pairing_selfdual_alternating", pairing_matrix([1, 26], [1, 26], 26, "alternating"),
                 5, 1, [], (1, 2, 3)),
    ]
    a = [2, 2, 2, 3]
    e = 7
    for k in range(1, 10):
        assert length([e * x for x in a], 0, e * k) == e * length(a, 0, k)
    output = {"status": "all exact checks passed", "cases": cases,
              "ramification_example": {"relative_ramification": e,
                "original_exponents": a, "extended_exponents": [e * x for x in a],
                "original_supremum": sum(a), "extended_supremum": e * sum(a),
                "normalized_supremum_over_Z5": sum(a)},
              "limits": "Abstract exact relation matrices; no arithmetic Galois image or Lean kernel claim."}
    path = Path(__file__).with_name("congruence_length_certificates.json")
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(output["status"])
    print(f"{len(cases)} matrix cases; ramification scaling checked; output: {path.name}")


if __name__ == "__main__":
    main()
