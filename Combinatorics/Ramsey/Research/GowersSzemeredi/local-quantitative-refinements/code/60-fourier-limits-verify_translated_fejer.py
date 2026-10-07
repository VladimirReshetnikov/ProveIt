#!/usr/bin/env python3
"""Exact rational checks for the translated Fejer restriction certificate.

These finite checks are diagnostics. General claims are proved in the notes.
No floating-point Fourier transform is used: the selector's survival probability
is evaluated by coefficient enumeration and exact character orthogonality.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, gcd
from pathlib import Path
import json
import random


def weights(length):
    return [(n, Fraction(length-abs(n), length*length))
            for n in range(1-length, length)]


def kernel_moment(m, length):
    coeffs = {0: Fraction(1)}
    for _ in range(m):
        out = Counter()
        for a, ca in coeffs.items():
            for b, cb in weights(length):
                out[a+b] += ca*cb
        coeffs = out
    return coeffs[0]


def choose(n, k):
    return comb(n, k) if n >= k >= 0 else 0


def kernel_moment_closed(m, length):
    numerator = sum((-1)**j * comb(2*m, j)
                    * choose((m-j)*length+m-1, 2*m-1)
                    for j in range(m+1))
    return Fraction(numerator, length**(2*m))


def signal(m, length, order=0):
    return sum((Fraction(length-abs(n), length))**m
               for n in range(1-length, length)
               if order == 0 or n % order == 0)


def run_case(domain_modulus, target_modulus, points, values, m, length):
    points = tuple(points)
    mapping = dict(zip(points, values))

    @lru_cache(None)
    def true_survival(selected_points):
        answer = Fraction(0)
        for coefficients in product(weights(length), repeat=len(selected_points)):
            ns = [n for n, _ in coefficients]
            if sum(ns):
                continue
            if sum(n*x for n, x in zip(ns, selected_points)) % domain_modulus:
                continue
            if sum(n*mapping[x] for n, x in zip(ns, selected_points)) % target_modulus:
                continue
            value = Fraction(1)
            for _, coefficient in coefficients:
                value *= coefficient
            answer += value
        return answer

    total = good = bad_repeated = 0
    expected_good = expected_bad = Fraction(0)
    leakage = Fraction(0)
    for xs in product(points, repeat=m):
        domain_error = sum(xs[:m//2])-sum(xs[m//2:])
        if domain_error % domain_modulus:
            continue
        total += 1
        target_error = (sum(mapping[x] for x in xs[:m//2])
                        - sum(mapping[x] for x in xs[m//2:])) % target_modulus
        survival = true_survival(tuple(sorted(set(xs))))
        if target_error == 0:
            good += 1
            expected_good += survival
        else:
            expected_bad += survival
            bad_repeated += len(set(xs)) < m
            error_order = target_modulus//gcd(target_modulus, target_error)
            leakage += signal(m, length, error_order)

    a = Fraction(1, length**m)
    s = signal(m, length)
    j = kernel_moment(m, length)
    tau = max(gcd(domain_modulus, d) for d in range(1, 2*length-1))
    bound_good = a*s*good
    bound_bad = (a*leakage + tau*(j-a*s)*len(points)**(m-2)
                 + (Fraction(1, length)-a)*bad_repeated)
    assert expected_good >= bound_good
    assert expected_bad <= bound_bad
    assert bad_repeated <= comb(m, 2)*len(points)**(m-2)
    assert a*s <= j <= Fraction(1, length)
    assert j == kernel_moment_closed(m, length)
    return {
        "domain_modulus": domain_modulus,
        "target_modulus": target_modulus,
        "points": points,
        "values": values,
        "tuple_length": m,
        "kernel_length": length,
        "total_tuples": total,
        "respected_tuples": good,
        "unrespected_repeated_tuples": bad_repeated,
        "expected_respected": str(expected_good),
        "expected_unrespected": str(expected_bad),
        "respected_lower_bound": str(bound_good),
        "unrespected_upper_bound": str(bound_bad),
        "torsion_factor": tau,
        "checked": True,
    }


def main():
    rng = random.Random(20261007)
    cases = []
    for domain_modulus, target_modulus in [
        (2, 2), (3, 3), (4, 2), (4, 4), (5, 5), (6, 4), (6, 6),
        (7, 7), (8, 3), (8, 8), (9, 9), (10, 6), (11, 11), (15, 9),
    ]:
        for length in [2, 3, 4]:
            for repeat in range(2):
                b = min(5, domain_modulus)
                points = sorted(rng.sample(range(domain_modulus), b))
                values = [rng.randrange(target_modulus) for _ in points]
                cases.append(run_case(domain_modulus, target_modulus,
                                      points, values, 4, length))
    # A higher-order check makes repeated nontrivial image errors abundant.
    for domain_modulus, target_modulus, values in [
        (3, 3, [0, 0, 1]), (4, 4, [0, 1, 3]),
        (5, 5, [0, 1, 4]), (6, 2, [0, 0, 1]),
    ]:
        cases.append(run_case(domain_modulus, target_modulus,
                              [0, 1, 2], values, 6, 3))

    coefficient_cases = 0
    for m in range(2, 11):
        for length in range(2, 12):
            s = signal(m, length)
            j = kernel_moment(m, length)
            a = Fraction(1, length**m)
            assert Fraction(2*length, m+1) <= s <= length
            assert a*s <= j <= Fraction(1, length)
            assert j == kernel_moment_closed(m, length)
            coefficient_cases += 1

    result = {
        "description": "Exact finite diagnostics; not substitutes for the proofs",
        "seed": 20261007,
        "selector_cases": len(cases),
        "coefficient_cases": coefficient_cases,
        "all_passed": True,
        "cases": cases,
    }
    destination = Path(__file__).with_name("translated_fejer_verification.json")
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"selector_cases": len(cases),
                      "coefficient_cases": coefficient_cases,
                      "all_passed": True,
                      "output": str(destination)}))


if __name__ == "__main__":
    main()
