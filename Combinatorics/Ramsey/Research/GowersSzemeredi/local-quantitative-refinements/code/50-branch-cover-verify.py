#!/usr/bin/env python3
"""Exact finite checks for branch-cover bounds; no third-party dependencies.

These checks do not instantiate the enormous Section 16.10 counterexample.
They test the finite inequalities used in its mathematical proof.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
import random
from fractions import Fraction
from pathlib import Path


def prime(p: int) -> bool:
    return p >= 2 and all(p % k for k in range(2, math.isqrt(p) + 1))


def ap_masks(p: int, min_length: int = 1) -> list[int]:
    if not prime(p) or not 1 <= min_length <= p:
        raise ValueError("Require a prime p and 1 <= min_length <= p")
    ans: set[int] = set()
    for a in range(p):
        for b in range(1, p):
            mask = 0
            for n in range(1, p + 1):
                mask |= 1 << ((a + (n - 1) * b) % p)
                if n >= min_length:
                    ans.add(mask)
    return sorted(ans, key=lambda z: (z.bit_count(), z))


def polynomial_values(p: int, degree: int) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    if not prime(p) or degree < 0:
        raise ValueError("Require prime modulus and nonnegative degree")
    return [(coef, tuple(sum(c * pow(x, i, p) for i, c in enumerate(coef)) % p
                         for x in range(p)))
            for coef in itertools.product(range(p), repeat=degree + 1)]


def empirical_cap(counts: list[int], q: int, per_nonconstant: int) -> int:
    """Upper bound max_s (sum of s heaviest counts + (q-s)*root bound)."""
    ordered = sorted(counts, reverse=True)
    return min(sum(counts), max(sum(ordered[:s]) + (q - s) * per_nonconstant
                               for s in range(min(q, len(counts)) + 1)))


def exhaustive_univariate() -> dict:
    p, R = 5, 3
    intervals = ap_masks(p)
    affine = polynomial_values(p, 1)
    quadratic = polynomial_values(p, 2)
    cases_affine = cases_quadratic = 0
    for word in itertools.product(range(R), repeat=p):
        matches1 = [sum((v == word[x]) << x for x, v in enumerate(values))
                    for _, values in affine]
        matches2 = [sum((v == word[x]) << x for x, v in enumerate(values))
                    for _, values in quadratic]
        for I in intervals:
            n = I.bit_count()
            counts = [sum(bool(I & (1 << x)) and word[x] == j for x in range(p))
                      for j in range(R)]
            masks = [v & I for v in matches1]
            for q in (0, 1, 2):
                cap = empirical_cap(counts, q, R)
                if q == 0:
                    candidates = [0]
                elif q == 1:
                    candidates = masks
                else:
                    candidates = (x | y for i, x in enumerate(masks)
                                  for y in masks[i:])
                best = 0
                for union in candidates:
                    size = union.bit_count()
                    assert size <= cap, (word, I, q, size, cap)
                    best = max(best, size)
                    cases_affine += 1
                top = sum(sorted(counts, reverse=True)[:q])
                assert best >= top
                if q > 0 and sorted(counts, reverse=True)[q - 1] >= R:
                    assert best == top
            cap2 = empirical_cap(counts, 1, 2 * R)
            for mask in matches2:
                assert (mask & I).bit_count() <= cap2
                cases_quadratic += 1
    return {"p": p, "alphabet_size": R, "words": R ** p,
            "distinct_AP_sets": len(intervals),
            "affine_list_checks_including_repetition": cases_affine,
            "quadratic_single_graph_checks": cases_quadratic}


def exhaustive_product() -> dict:
    p, R = 3, 2
    sets = ap_masks(p)
    polys = list(itertools.product(range(p), repeat=4))
    checks = 0
    for word in itertools.product(range(R), repeat=p):
        masks = []
        for c, a, b, d in polys:
            masks.append(sum((((c + a * h + b * y + d * h * y) % p) == word[y])
                             << (p * h + y) for h in range(p) for y in range(p)))
        for T in sets:
            for I in sets:
                box = sum(1 << (p * h + y) for h in range(p) for y in range(p)
                          if T & (1 << h) and I & (1 << y))
                counts = [sum(bool(I & (1 << y)) and word[y] == j for y in range(p))
                          for j in range(R)]
                cap = T.bit_count() * empirical_cap(counts, 2, R)
                covered = [mask & box for mask in masks]
                for i, a in enumerate(covered):
                    for b in covered[i:]:
                        assert (a | b).bit_count() <= cap
                        checks += 1
    return {"p": p, "alphabet_size": R, "words": R ** p,
            "boxes_per_word": len(sets) ** 2, "bilinear_pair_checks": checks}


def toy_certificate() -> dict:
    """Check every AP of length at least 128 in a fixed word over F_257.

    Integer comparisons only. This is a small analogue, not the specific
    Section 16.10 instance, whose parameters are vastly larger.
    """
    p, R, L, seed = 257, 4, 128, 20261006
    rng = random.Random(seed)
    word = [rng.randrange(R) for _ in range(p)]
    max_mass = Fraction(0)
    min_mass = Fraction(1)
    witness = None
    tests = 0
    for step in range(1, p):
        seq = [word[(i * step) % p] for i in range(2 * p)]
        prefix = [[0] * (2 * p + 1) for _ in range(R)]
        for j in range(R):
            for i, v in enumerate(seq):
                prefix[j][i + 1] = prefix[j][i] + (v == j)
        for start in range(p):
            for n in range(L, p + 1):
                for j in range(R):
                    count = prefix[j][start + n] - prefix[j][start]
                    if count * max_mass.denominator > max_mass.numerator * n:
                        max_mass = Fraction(count, n)
                        witness = {"start": (start * step) % p,
                                   "step": step, "length": n, "symbol": j}
                    if count * min_mass.denominator < min_mass.numerator * n:
                        min_mass = Fraction(count, n)
                    assert count >= R  # exact optimal-list theorem for q <= R
                    tests += 1
    assert max_mass < Fraction(1, 2)
    return {"p": p, "alphabet_size": R, "min_AP_length": L, "seed": seed,
            "word": word, "AP_parameterizations": p * (p - 1) * (p - L + 1),
            "symbol_frequency_checks": tests,
            "maximum_symbol_fraction": str(max_mass),
            "minimum_symbol_fraction": str(min_mass),
            "maximum_witness": witness,
            "conclusion": "On every tested AP, every affine graph covers < 1/2; the best q<=4 polynomial lists of degree one are given by the q heaviest constants."}


def exhaustive_quadratic_nonvacuous() -> dict:
    p, R = 7, 2
    intervals = ap_masks(p)
    polynomials = polynomial_values(p, 2)
    checks = nonvacuous = 0
    for word in itertools.product(range(R), repeat=p):
        matches = [sum((v == word[x]) << x for x, v in enumerate(values))
                   for _, values in polynomials]
        for I in intervals:
            counts = [sum(bool(I & (1 << x)) and word[x] == j for x in range(p))
                      for j in range(R)]
            cap = empirical_cap(counts, 1, 2 * R)
            for match in matches:
                assert (match & I).bit_count() <= cap
                checks += 1
                nonvacuous += cap < I.bit_count()
    return {"p": p, "alphabet_size": R, "words": R ** p,
            "distinct_AP_sets": len(intervals), "checks": checks,
            "checks_with_cap_strictly_below_set_size": nonvacuous}


def endpoint_test() -> dict:
    p = 3
    affine = {tuple((a * x + b) % p for x in range(p))
              for a in range(p) for b in range(p)}
    bilinear = {tuple((c + a * h + b * y + d * h * y) % p
                      for h in range(p) for y in range(p))
                for c, a, b, d in itertools.product(range(p), repeat=4)}
    accepted = 0
    for table in itertools.product(range(p), repeat=p*p):
        row_ok = all(tuple(table[p*h+y] for y in range(p)) in affine for h in range(p))
        col_ok = all(tuple(table[p*h+y] for h in range(p)) in affine for y in range(p))
        assert (row_ok and col_ok) == (table in bilinear)
        accepted += row_ok and col_ok
    return {"p": p, "full_domain_functions_checked": p ** (p*p),
            "separately_affine_equals_bilinear_count": accepted,
            "scope": "Tests the finite separate-affinity characterization, not all real-weight product-property inequalities."}


def scalar_tests() -> dict:
    cases = 0
    for E in range(2, 11):
        Q = 2 ** E
        R = 4 * Q
        for r in range(2, 8):
            assert (2 * r) ** (E * r) >= R
            assert Fraction(Q, R) * Fraction(5, 4) == Fraction(5, 16)
            cases += 1
    return {"integer_budget_checks": cases,
            "note": "Only reduced exponents are numerically instantiated; the article proves the inequalities for all exponents."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "verification.json")
    parser.add_argument("--skip-toy", action="store_true")
    args = parser.parse_args()
    result = {"status": "PASS", "arithmetic": "exact integer/rational",
              "univariate": exhaustive_univariate(),
              "product": exhaustive_product(), "quadratic_nonvacuous": exhaustive_quadratic_nonvacuous(),
              "endpoint": endpoint_test(), "scalar": scalar_tests()}
    if not args.skip_toy:
        result["toy_certificate"] = toy_certificate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: (v if k != "toy_certificate" else {a: b for a, b in v.items() if a != "word"})
                      for k, v in result.items()}, indent=2))

if __name__ == "__main__":
    main()
