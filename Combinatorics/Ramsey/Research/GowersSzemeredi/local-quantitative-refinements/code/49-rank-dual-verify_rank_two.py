#!/usr/bin/env python3
"""Exact finite checks for the rank-two translation-containment theorem.

Only Python's standard library is used. The general theorem has a separate
human proof; these checks verify its small-dimensional classifications,
the finite singleton table, and direct finite-field translation counts.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod
from pathlib import Path
import json


if not __debug__:
    raise SystemExit("Verification refuses python -O; use ordinary python3.")


def coefficients(values, k):
    result = list(values)
    for i in range(k):
        for mask in range(1 << k):
            if mask & (1 << i):
                result[mask] -= result[mask ^ (1 << i)]
    return tuple(result)


def field_rank(matrix, p):
    a = [[x % p for x in row] for row in matrix]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        scale = pow(a[rank][col], -1, p)
        a[rank] = [(x * scale) % p for x in a[rank]]
        for i in range(len(a)):
            if i != rank and a[i][col]:
                scale = a[i][col]
                a[i] = [(x - scale * y) % p
                        for x, y in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def derivative_rank(c, k, p):
    matrix = [[0 if mask & (1 << i) else c[mask | (1 << i)]
               for mask in range(1 << k)] for i in range(k)]
    return field_rank(matrix, p)


def evaluate(c, point, p):
    total = 0
    for mask, coefficient in enumerate(c):
        term = coefficient
        for i, x in enumerate(point):
            if mask & (1 << i):
                term *= x
        total += term
    return total % p


def signed_divisor(t, p):
    return (any(x % p in (0, 1, p - 1) for x in t)
            or any((t[i] - t[j]) % p == 0
                   or (t[i] + t[j]) % p == 0
                   for i in range(len(t)) for j in range(i)))


def translated_is_ternary(c, t, k, p):
    return all(evaluate(c, tuple(t[i] + ((mask >> i) & 1)
                                 for i in range(k)), p) in (0, 1, p - 1)
               for mask in range(1 << k))


def binomial(k, j):
    return comb(k, j) if j <= k else 0


def count_rank_two(k):
    return (62 * binomial(k, 2) + 84 * binomial(k, 3)
            + 24 * binomial(k, 4))


def singleton_table():
    groups = defaultdict(list)
    for A, B, C, D in product((-1, 0, 1), repeat=4):
        a = A - B - C + D
        if a > 0:
            groups[a, A * D - B * C].append((C - A, B - A))
    pair_count = 0
    for (a, _), slopes in groups.items():
        for (c, b), (cc, bb) in product(slopes, repeat=2):
            u, v = Fraction(cc - c, a), Fraction(bb - b, a)
            assert u in (-1, 0, 1) or v in (-1, 0, 1) or u == v or u == -v
            pair_count += 1
    assert sum(map(len, groups.values())) == 31
    assert len(groups) == 11
    return {
        "positive_quadratic_patterns": 31,
        "invariant_rows": 11,
        "ordered_pairs_checked": pair_count,
        "rows": [{"a": a, "determinant": d, "slopes_c_b": slopes}
                 for (a, d), slopes in sorted(groups.items())],
    }


def rank_census():
    out = []
    for k in (1, 2, 3):
        polys = [coefficients(values, k)
                 for values in product((-1, 0, 1), repeat=1 << k)]
        for p in (5, 7, 11, 13):
            counts = Counter(derivative_rank(c, k, p) for c in polys)
            assert counts[0] == 3
            assert counts[1] == 6 * k + 4 * binomial(k, 2)
            assert counts[2] == count_rank_two(k)
            rank_two_support = Counter()
            for c in polys:
                if derivative_rank(c, k, p) == 2:
                    support = sum(any(c[mask] % p and mask & (1 << i)
                                      for mask in range(1 << k))
                                  for i in range(k))
                    rank_two_support[support] += 1
            assert rank_two_support[2] == 62 * binomial(k, 2)
            assert rank_two_support[3] == 84 * binomial(k, 3)
            out.append({"k": k, "prime": p,
                        "derivative_rank_counts": dict(sorted(counts.items())),
                        "rank_two_essential_support_counts":
                            dict(sorted(rank_two_support.items()))})
    return out


def exact_k2_counts():
    polys = [coefficients(values, 2)
             for values in product((-1, 0, 1), repeat=4)]
    nonconstant = [c for c in polys if any(c[1:])]
    out = []
    for p in (3, 5, 7, 11, 13, 17, 19):
        bad = {t for t in product(range(p), repeat=2)
               if any(translated_is_ternary(c, t, 2, p)
                      for c in nonconstant)}
        divisor = {t for t in product(range(p), repeat=2)
                   if signed_divisor(t, p)}
        assert bad == divisor
        complement = (p - 3) * (p - 5)
        assert len(bad) == p * p - complement
        delta = 1 - Fraction((p - 1) ** 2 * complement, p ** 4)
        formula = (Fraction(10, p) - Fraction(32, p ** 2)
                   + Fraction(38, p ** 3) - Fraction(15, p ** 4))
        assert delta == formula
        out.append({"prime": p, "bad_translation_count": len(bad),
                    "nondegenerate_translation_count": complement,
                    "arrangement_degeneracy_proportion": str(delta)})
    return out


def rank_two_k3_translation_checks():
    all_polys = [coefficients(v, 3)
                 for v in product((-1, 0, 1), repeat=8)]
    out = []
    for p in (11, 13):
        polys = [c for c in all_polys if derivative_rank(c, 3, p) == 2]
        outside = [t for t in product(range(p), repeat=3)
                   if not signed_divisor(t, p)]
        assert len(outside) == prod(p - 2 * i - 1 for i in range(1, 4))
        successes = sum(translated_is_ternary(c, t, 3, p)
                        for t in outside for c in polys)
        assert successes == 0
        out.append({"prime": p, "rank_two_polynomials": len(polys),
                    "outside_divisor_translations": len(outside),
                    "polynomial_translation_pairs_checked": len(polys) * len(outside),
                    "extra_successes": successes})
    return out


def coefficient_checks():
    out = []
    for k in range(1, 13):
        weights = [1] * k + list(range(3, 2 * k + 2, 2))
        first = sum(weights)
        second = sum(a * b for a, b in combinations(weights, 2))
        assert first == k * k + 3 * k
        assert second == k * (3 * k ** 3 + 14 * k * k + 15 * k - 14) // 6
        out.append({"k": k, "coefficient_p_inverse": first,
                    "negative_coefficient_p_inverse_squared": second})
    return out


if __name__ == "__main__":
    report = {
        "scope": "Finite exact checks supplementing a separate general proof",
        "arithmetic": "Python integers, fractions, and prime-field Gaussian elimination",
        "singleton_invariant_table": singleton_table(),
        "rank_censuses": rank_census(),
        "exact_dimension_two_counts": exact_k2_counts(),
        "dimension_three_rank_two_checks": rank_two_k3_translation_checks(),
        "second_coefficient_checks": coefficient_checks(),
        "all_checks_passed": True,
    }
    target = Path(__file__).with_name("rank_two_verification.json")
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"all_checks_passed": True, "output": str(target),
                      "rank_census_cases": len(report["rank_censuses"]),
                      "exact_k2_cases": len(report["exact_dimension_two_counts"]),
                      "rank_two_translation_pairs_checked": sum(
                          r["polynomial_translation_pairs_checked"]
                          for r in report["dimension_three_rank_two_checks"])}))
