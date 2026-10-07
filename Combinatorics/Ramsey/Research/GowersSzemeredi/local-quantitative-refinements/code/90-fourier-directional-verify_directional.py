#!/usr/bin/env python3
"""Exact bounded checks for the cyclic directional comparison.

This is a regression and finite verification companion. The proof for all
groups and N >= 12 is in gowers_fourier_directional.tex, not in this program.
Only Python's standard library is required. No floating point is used.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
import json
import random


def demand(condition, message):
    if not condition:
        raise RuntimeError(message)


def defects(values, modulus):
    n = len(values)
    numerators = []
    for h in range(n):
        counts = Counter(
            (values[(x + h) % n] - values[x]) % modulus
            for x in range(n)
        )
        numerators.append(n * n - sum(c * c for c in counts.values()))
    return Fraction(sum(numerators), n**3), Fraction(numerators[1], n * n)


def increment_multiplicities(values, modulus):
    n = len(values)
    return sorted(
        Counter((values[(i + 1) % n] - values[i]) % modulus
                for i in range(n)).values(),
        reverse=True,
    )


def check_map(values, modulus, equality_required=False):
    n = len(values)
    total, local = defects(values, modulus)
    demand(total <= Fraction(n + 1, 6) * local,
           f"Cycle inequality failed: N={n}, modulus={modulus}, f={values}")
    if n >= 12:
        actual_equality = total == Fraction(n + 1, 6) * local
        expected_equality = increment_multiplicities(values, modulus) in (
            [n], [n - 1, 1]
        )
        demand(actual_equality == expected_equality,
               f"Equality classification failed for N={n}, f={values}")
    if equality_required:
        demand(total == Fraction(n + 1, 6) * local,
               "Expected sawtooth equality failed")
    return total, local


def check_windows():
    pair_count = 0
    equality_pairs = []
    for n in range(2, 49):
        single_count = sum(2 * h * (n - h) for h in range(n))
        demand(Fraction(single_count, n**3) == Fraction(n*n-1, 3*n*n),
               f"Single-window formula failed for N={n}")
        for d in range(1, n // 2 + 1):
            pair_numerator = 0
            for h in range(n):
                pattern_counts = [0] * 4
                for x in range(n):
                    window = {(x + j) % n for j in range(h)}
                    pattern = int(0 in window) + 2 * int(d in window)
                    pattern_counts[pattern] += 1
                pair_numerator += 2 * (
                    pattern_counts[0] * pattern_counts[3]
                    + pattern_counts[1] * pattern_counts[2]
                )
            empirical = Fraction(pair_numerator, n**3)
            formula = Fraction(
                n**3 - 6*d*n*n + 18*d*d*n - 16*d**3 + 4*d - n,
                3*n**3,
            )
            demand(empirical == formula,
                   f"Pair-window formula failed for N={n}, d={d}")
            demand(empirical >= Fraction(1, 8),
                   f"Pair-window lower bound failed for N={n}, d={d}")
            expected_equality = 4*d == n
            demand((empirical == Fraction(1, 8)) == expected_equality,
                   f"Pair-window equality failed for N={n}, d={d}")
            if expected_equality:
                equality_pairs.append([n, d])
            pair_count += 1
    return {"N_range": [2, 48], "pairs_checked": pair_count,
            "equality_pairs": equality_pairs}


def check_finite_functions():
    records = []
    for n, p in [(3, 7), (4, 7), (5, 7), (6, 5), (7, 4), (8, 3)]:
        maximum = Fraction(0)
        witness = None
        count = 0
        for tail in product(range(p), repeat=n-1):
            values = (0,) + tail
            total, local = check_map(values, p)
            if local:
                ratio = total / local
                if ratio > maximum:
                    maximum, witness = ratio, list(values)
            count += 1
        records.append({"N": n, "target_modulus": p,
                        "normalized_functions_checked": count,
                        "maximum_ratio": str(maximum),
                        "witness": witness,
                        "comparison_constant": str(Fraction(n+1, 6))})
    return records


def check_theorem_range():
    rng = random.Random(1072026)
    random_count = 0
    structured_count = 0
    sawtooth_count = 0
    for n in [12, 13, 16, 19, 24, 31, 48, 64]:
        for p in [2, 3, 5, 7, 11]:
            for unused in range(40):
                check_map([rng.randrange(p) for i in range(n)], p)
                random_count += 1
            for s in range(1, 6):
                for unused in range(12):
                    majority = rng.randrange(p)
                    increments = [majority] * n
                    indices = rng.sample(range(n), s)
                    for i in indices[:-1]:
                        increments[i] = rng.randrange(p)
                    last = indices[-1]
                    increments[last] = -(sum(increments) - increments[last]) % p
                    demand(sum(increments) % p == 0, "Invalid constructed cycle")
                    values = [0]
                    for a in increments[:-1]:
                        values.append((values[-1] + a) % p)
                    check_map(values, p)
                    structured_count += 1
            for a in range(p):
                if n*a % p:
                    total, local = check_map([(a*j) % p for j in range(n)], p,
                                             equality_required=True)
                    demand(total == Fraction(n*n-1, 3*n*n),
                           "Sawtooth uniform defect formula failed")
                    demand(local == Fraction(2*(n-1), n*n),
                           "Sawtooth local defect formula failed")
                    sawtooth_count += 1
    for n in range(12, 501):
        for s in [2, 3, 4]:
            demand(8*s*(n+1) < 3*n*n, "Small-minority proof gate failed")
        demand(2*n*n-20*n-25 > 0, "Large-minority proof gate failed")
    return {"random_seed": 1072026, "random_maps": random_count,
            "structured_maps": structured_count, "sawtooth_maps": sawtooth_count,
            "proof_gate_N_range": [12, 500]}


def twelve_point_example():
    n, p = 12, 5
    values = [i % p for i in range(n)]
    total, local = check_map(values, p, equality_required=True)
    rejected = 0
    for h, x, y in product(range(n), repeat=3):
        rejected += (values[(x+h) % n] - values[x]
                     - values[(y+h) % n] + values[y]) % p != 0
    demand(rejected == 572, "Twelve-point rejected-count mismatch")
    demand(n**3 - rejected == 1156, "Twelve-point graph-energy mismatch")
    demand(total == Fraction(143, 432), "Twelve-point total defect mismatch")
    demand(local == Fraction(11, 72), "Twelve-point local defect mismatch")
    return {"N": n, "target_modulus": p, "uniform_defect": str(total),
            "local_defect": str(local), "rejected_parallelograms": rejected,
            "graph_energy": n**3-rejected}


def main():
    result = {
        "status": "PASS",
        "arithmetic": "exact integers and fractions; no floating point",
        "scope": "bounded independent checks; not a substitute for the proof",
        "window_checks": check_windows(),
        "small_exhaustive_checks": check_finite_functions(),
        "theorem_range_checks": check_theorem_range(),
        "twelve_point_example": twelve_point_example(),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
