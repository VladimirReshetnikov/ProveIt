#!/usr/bin/env python3
"""Exact finite checks for the discriminant -23 Hecke-GRH research target.

Python standard library only. No network, external executables, or downloaded code.

The calculations support the algebraic description in the accompanying report.
They do not prove GRH, certify the grh-lean project, establish novelty, or replace
the standard theorems connecting reduced forms, class fields, and Artin L-series.

Run: python3 arithmetic_checks.py --output arithmetic_checks.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path


SNAPSHOT = "72fead102f663d5c7a407964a13dc0cf9d977207"
Polynomial = tuple[int, ...]  # Ascending coefficients, constant coefficient first.
Permutation = tuple[int, ...]


def check(condition: bool, message: str) -> None:
    """Keep checks active even when Python is invoked with -O."""
    if not condition:
        raise AssertionError(message)


def trim(poly: Polynomial) -> Polynomial:
    result = list(poly)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def multiply(p: Polynomial, q: Polynomial) -> Polynomial:
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(tuple(out))


def power(p: Polynomial, exponent: int) -> Polynomial:
    out = (1,)
    for _ in range(exponent):
        out = multiply(out, p)
    return out


def one_minus_t_power(exponent: int) -> Polynomial:
    return (1,) + (0,) * (exponent - 1) + (-1,)


def polynomial_value(p: Polynomial, x: int) -> int:
    out = 0
    for coefficient in reversed(p):
        out = out * x + coefficient
    return out


def compose(p: Permutation, q: Permutation) -> Permutation:
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p: Permutation) -> Permutation:
    return tuple(p.index(i) for i in range(len(p)))


def cycle_lengths(p: Permutation) -> tuple[int, ...]:
    unused = set(range(len(p)))
    lengths = []
    while unused:
        start = min(unused)
        current, length = start, 0
        while current in unused:
            unused.remove(current)
            current = p[current]
            length += 1
        lengths.append(length)
    return tuple(sorted(lengths))


def permutation_sign(p: Permutation) -> int:
    inversions = sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))
    return (-1) ** inversions


def reduced_forms(discriminant: int) -> dict:
    """Enumerate all primitive reduced positive binary forms at this D.

    Standard reduction conditions are |b| <= a <= c, with b >= 0 if either
    |b| = a or a = c. They imply |D|=4ac-b^2 >= 3a^2. Hence iterating
    3a^2 <= |D| is exhaustive under those conditions, with no float rounding.
    """
    check(discriminant < 0, "Negative discriminant required")
    upper_a = math.isqrt((-discriminant) // 3)
    forms = []
    for a in range(1, upper_a + 1):
        for b in range(-a, a + 1):
            numerator = b * b - discriminant
            if numerator % (4 * a):
                continue
            c = numerator // (4 * a)
            if a > c or ((abs(b) == a or a == c) and b < 0):
                continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1:
                continue
            check(b * b - 4 * a * c == discriminant, "Discriminant mismatch")
            forms.append((a, b, c))
    expected = [(1, 1, 6), (2, -1, 3), (2, 1, 3)]
    check(forms == expected, "Unexpected reduced-form list")
    return {
        "discriminant": discriminant,
        "bound": "3*a^2 <= 23, equivalently a <= sqrt(23/3)",
        "maximum_a": upper_a,
        "forms": forms,
        "number_of_forms": len(forms),
        "exhaustive_under_standard_reduction_conditions": True,
        "class_number_interpretation": "h(Q(sqrt(-23)))=3 by the standard reduced-form/ideal-class correspondence",
    }


def polynomial_checks() -> dict:
    # For a*x^3+b*x^2+c*x+d the discriminant is
    # b^2*c^2-4*a*c^3-4*b^3*d-27*a^2*d^2+18*a*b*c*d.
    a, b, c, d = 1, 0, -1, -1
    discr = b * b * c * c - 4 * a * c**3 - 4 * b**3 * d - 27 * a * a * d * d + 18 * a * b * c * d
    check(discr == -23, "Cubic discriminant mismatch")
    poly = (d, c, b, a)
    roots_test = {str(r): polynomial_value(poly, r) for r in (-1, 1)}
    check(all(v != 0 for v in roots_test.values()), "Unexpected rational root")
    factorization = multiply(power((-10, 1), 2), (-3, 1))
    check(tuple(x % 23 for x in factorization) == tuple(x % 23 for x in poly), "Wrong mod-23 factorization")
    derivative = (-1, 0, 3)
    second_derivative = (0, 6)
    check(polynomial_value(derivative, 10) % 23 == 0, "Double root not multiple")
    check(polynomial_value(second_derivative, 10) % 23 != 0, "Double root unexpectedly triple")
    check(polynomial_value(derivative, 3) % 23 != 0, "Simple root unexpectedly multiple")
    roots = [r for r in range(23) if polynomial_value(poly, r) % 23 == 0]
    check(roots == [3, 10], "Unexpected roots modulo 23")
    return {
        "polynomial_ascending_coefficients": poly,
        "discriminant": discr,
        "rational_root_candidates_and_values": roots_test,
        "irreducibility_reason": "Monic cubic; rational roots must be integer divisors of -1; neither +1 nor -1 is a root",
        "mod_23_factorization": "(x-10)^2*(x-3) = (x+13)^2*(x+20) mod 23",
        "mod_23_roots": [{"root": 10, "multiplicity": 2}, {"root": 3, "multiplicity": 1}],
        "squarefree_discriminant": True,
    }


def s3_and_euler_checks() -> dict:
    group = list(itertools.permutations(range(3)))
    identity = (0, 1, 2)
    rows = []
    for p in group:
        cycles = cycle_lengths(p)
        fixed = sum(p[i] == i for i in range(3))
        sign = permutation_sign(p)
        standard = fixed - 1
        regular = 6 if p == identity else 0
        check(fixed == 1 + standard, "Permutation character decomposition failed")
        check(regular == 1 + sign + 2 * standard, "Regular character decomposition failed")
        induced = 2 if p == identity else (-1 if cycles == (3,) else 0)
        check(induced == standard, "Induced order-three character trace mismatch")

        # Character inner products below verify irreducibility and orthogonality.
        # Euler denominators are det(1-t*Frob) on the corresponding spaces.
        order = math.lcm(*cycles)
        permutation_denominator = (1,)
        for length in cycles:
            permutation_denominator = multiply(permutation_denominator, one_minus_t_power(length))
        standard_denominator = (1, -standard, sign)
        regular_denominator = power(one_minus_t_power(order), 6 // order)
        check(permutation_denominator == multiply((1, -1), standard_denominator), "Cubic local Euler identity failed")
        check(regular_denominator == multiply(multiply((1, -1), (1, -sign)), power(standard_denominator, 2)), "Normal-closure local Euler identity failed")
        rows.append({
            "permutation": p,
            "cycle_lengths": cycles,
            "trivial_character": 1,
            "sign_character": sign,
            "standard_character": standard,
            "permutation_character": fixed,
            "regular_character": regular,
            "induced_nontrivial_A3_character": induced,
            "cubic_zeta_denominator": permutation_denominator,
            "standard_L_denominator": standard_denominator,
            "normal_closure_zeta_denominator": regular_denominator,
        })
    character_names = ["trivial_character", "sign_character", "standard_character"]
    gram = [[Fraction(sum(row[left] * row[right] for row in rows), 6)
             for right in character_names] for left in character_names]
    check(gram == [[Fraction(int(i == j)) for j in range(3)] for i in range(3)], "Character orthonormality failed")

    # At 23, squarefree discriminant and tame ramification give inertia C2.
    # Its normalizer in S3 is itself; hence D=I and the residue Frobenius is
    # trivial. Local Euler factors are (1-t)^dim(V^I).
    transposition = (1, 0, 2)
    inertia = {identity, transposition}
    normalizer = [g for g in group if {compose(compose(g, h), inverse(g)) for h in inertia} == inertia]
    check(set(normalizer) == inertia, "Inertia normalizer differs from C2")
    inertia_rows = [r for r in rows if r["permutation"] in inertia]
    invariant_dimensions = {name: Fraction(sum(r[name] for r in inertia_rows), 2)
                            for name in character_names + ["permutation_character", "regular_character"]}
    check(invariant_dimensions == {
        "trivial_character": 1, "sign_character": 0, "standard_character": 1,
        "permutation_character": 2, "regular_character": 3,
    }, "Ramified invariant dimension mismatch")
    ramified_standard = (1, -1)
    ramified_sign = (1,)
    ramified_cubic = power((1, -1), 2)
    ramified_regular = power((1, -1), 3)
    check(ramified_cubic == multiply((1, -1), ramified_standard), "Ramified cubic Euler identity failed")
    check(ramified_regular == multiply(multiply((1, -1), ramified_sign), power(ramified_standard, 2)), "Ramified normal-closure Euler identity failed")
    return {
        "polynomial_encoding": "Ascending integer coefficients in t=p^(-s)",
        "all_six_elements": rows,
        "character_gram_matrix": [[str(x) for x in row] for row in gram],
        "character_decompositions": ["permutation_3 = trivial + standard_2", "regular_6 = trivial + sign + 2*standard_2"],
        "ramified_23": {
            "inertia_generator": transposition,
            "normalizer_equals_inertia": True,
            "invariant_dimensions": {k: str(v) for k, v in invariant_dimensions.items()},
            "sign_L_denominator": ramified_sign,
            "standard_L_denominator": ramified_standard,
            "cubic_zeta_denominator": ramified_cubic,
            "normal_closure_zeta_denominator": ramified_regular,
        },
    }


def theta_coefficients(form: tuple[int, int, int], limit: int) -> list[int]:
    a, b, c = form
    disc_abs = 4 * a * c - b * b
    check(disc_abs > 0 and a > 0, "Positive definite form required")
    coeffs = [0] * (limit + 1)
    # 4*a*Q(x,y) = (2*a*x+b*y)^2 + |D|*y^2. These exact bounds
    # include every lattice vector with Q(x,y)<=limit, including signs.
    max_y = math.isqrt((4 * a * limit) // disc_abs)
    for y in range(-max_y, max_y + 1):
        width = math.isqrt(4 * a * limit - disc_abs * y * y)
        low_numerator = -width - b * y
        high_numerator = width - b * y
        low_x = -((-low_numerator) // (2 * a))  # exact ceiling
        high_x = high_numerator // (2 * a)
        for x in range(low_x, high_x + 1):
            value = a * x * x + b * x * y + c * y * y
            check(0 <= value <= limit, "Theta enumeration bound failure")
            coeffs[value] += 1
    return coeffs


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def theta_checks() -> dict:
    limit = 100
    principal = theta_coefficients((1, 1, 6), limit)
    other = theta_coefficients((2, 1, 3), limit)
    check(all((a - b) % 2 == 0 for a, b in zip(principal, other)), "Nonintegral half-difference coefficient")
    coeffs = [(a - b) // 2 for a, b in zip(principal, other)]
    check(coeffs[:7] == [0, 1, -1, -1, 0, 0, 1], "Initial theta coefficients mismatch")
    rows = []
    for p in range(2, 98):
        if not is_prime(p) or p == 23:
            continue
        roots = [x for x in range(p) if (x * x * x - x - 1) % p == 0]
        expected = len(roots) - 1
        check(coeffs[p] == expected, f"Prime coefficient mismatch at p={p}")
        rows.append({"prime": p, "roots_mod_p": roots, "root_count": len(roots),
                     "theta_coefficient": coeffs[p], "standard_trace_root_count_minus_one": expected})
    check(coeffs[23] == 1, "Ramified coefficient mismatch at 23")
    return {
        "status": "Finite exact consistency check only; not a proof of the all-prime identity or GRH",
        "formula": "(Theta_(1,1,6)-Theta_(2,1,3))/2",
        "coefficient_limit": limit,
        "coefficients_indexed_from_n_0": coeffs,
        "prime_comparisons": rows,
        "number_of_unramified_prime_comparisons": len(rows),
        "ramified_coefficient_a_23": coeffs[23],
        "eta_product_identity_tested": False,
    }


def principal_selector_checks() -> dict:
    rows = []
    for f in (1, 3):
        g = 3 // f
        prefactor = Fraction(g * f, 3)
        check(prefactor == 1, "Incorrect local logarithmic-derivative prefactor")
        local_coefficients = [prefactor if k % f == 0 else Fraction(0) for k in range(1, 21)]
        selector_coefficients = [int(k % f == 0) for k in range(1, 21)]
        check(local_coefficients == selector_coefficients, "Principal-class selector mismatch")
        rows.append({"class_order_f": f, "number_of_primes_above_g": g,
                     "normalized_log_derivative_prefactor_gf_over_3": str(prefactor),
                     "coefficients_k_1_to_20": [str(x) for x in local_coefficients]})
    return {
        "symbolic_identity": "(1/3)*u*d/du log((1-u^f)^(-3/f)) = u^f/(1-u^f), f in {1,3}",
        "interpretation": "After dividing by log(Np), -(1/3)*zeta_H'/zeta_H has coefficient 1 exactly when f divides k, equivalently p^k is principal in Cl(K)",
        "checks": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    report = {
        "all_assertions_passed": True,
        "purpose": "Exact finite arithmetic checks for a proposed Hecke-GRH transfer target",
        "grh_lean_snapshot_discussed": SNAPSHOT,
        "limitations": [
            "No claim to prove any Riemann hypothesis or a new theorem of analytic number theory",
            "No Lean compilation or independent proof-kernel certification performed by this script",
            "Class-field interpretations use standard mathematical theorems stated in the accompanying report",
            "The prime/theta comparison is finite evidence only",
        ],
        "reduced_forms": reduced_forms(-23),
        "cubic_polynomial": polynomial_checks(),
        "s3_and_euler_factors": s3_and_euler_checks(),
        "theta_consistency": theta_checks(),
        "principal_ideal_selector": principal_selector_checks(),
    }
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print("PASS: reduced forms of discriminant -23: (1,1,6), (2,-1,3), (2,1,3)")
    print("PASS: cubic discriminant, rational-root test, and exact mod-23 factorization")
    print("PASS: all six S3 characters, orthogonality, and unramified Euler identities")
    print("PASS: inertia normalizer, invariant dimensions, and ramified Euler factors at 23")
    print("PASS: 24 unramified prime/theta coefficient comparisons through p=97; a_23=1")
    print("PASS: principal-class local selector for f=1,3 and powers k=1,...,20")
    print("Finite checks do not prove GRH or certify grh-lean.")
    print(f"JSON output: {args.output.resolve()}")


if __name__ == "__main__":
    main()
