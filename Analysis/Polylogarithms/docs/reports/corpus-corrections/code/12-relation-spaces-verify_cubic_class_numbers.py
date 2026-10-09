#!/usr/bin/env python3
"""Exact finite certificates for the five cubic class-number-one proofs.

Uses only Python integer arithmetic. This verifies the elementary arithmetic
premises of the argument in corrections_gamma.tex; the deduction uses
Dedekind's index/factorization criteria and Minkowski's theorem as proved there.
Polynomial coefficients and generator coefficients are in increasing order.
"""
from __future__ import annotations
import argparse
import json
from math import isqrt
from pathlib import Path

FIELDS = [
    (37, [1, -3, -1, 1], {2: [-1, 1, 0]}),
    (101, [-1, -5, -1, 1], {2: [1, 1, 0], 3: [-2, -2, 1]}),
    (197, [-3, -7, -1, 1], {2: [1, 1, 0], 3: [0, 1, 0], 5: [-4, -2, 1]}),
    (257, [3, -4, -1, 1], {3: [0, 1, 0]}),
    (677, [-7, -11, -1, 1], {2: [1, 1, 0], 3: [2, 1, 0],
          5: [10, 2, -1], 7: [0, 1, 0], 11: [-17, -4, 2]}),
]


def evaluate(coeffs, x):
    value = 0
    for c in reversed(coeffs):
        value = value*x + c
    return value


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


def matmul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)]
            for i in range(3)]


def determinant(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def norm(poly, element):
    c0, c1, c2, leading = poly
    assert leading == 1
    mult_x = [[0, 0, -c0], [1, 0, -c1], [0, 1, -c2]]
    mult_x2 = matmul(mult_x, mult_x)
    a, b, c = element
    matrix = [[a*int(i == j) + b*mult_x[i][j] + c*mult_x2[i][j]
               for j in range(3)] for i in range(3)]
    return determinant(matrix)


def verify_field(d, f, generators):
    c, b, a, leading = f
    assert leading == 1
    possible_integer_roots = [r for r in range(-abs(c), abs(c)+1)
                              if r and c % r == 0]
    assert all(evaluate(f, r) != 0 for r in possible_integer_roots)
    disc = a*a*b*b - 4*b*b*b - 4*a*a*a*c - 27*c*c + 18*a*b*c
    assert prime(d) and disc in (d, 4*d) and disc > 0
    # Positive cubic discriminant gives three distinct real roots.
    # The square of the index divides disc. Only 2 can divide an index here.
    if disc == d:
        index_certificate = {"method": "squarefree discriminant"}
    else:
        cube = [1, 3, 3, 1]  # (X+1)^3
        assert all((u-v) % 2 == 0 for u, v in zip(f, cube))
        quotient = [(u-v)//2 for u, v in zip(f, cube)]
        test = evaluate(quotient, 1)
        assert test % 2 == 1
        index_certificate = {"method": "Dedekind index criterion at 2",
                             "f_mod_2": "(X+1)^3",
                             "correction_at_one": test}
    # Maximality is now proved, so polynomial discriminant = field discriminant.
    bound = isqrt(4*disc)//9
    assert (9*bound)**2 <= 4*disc < (9*(bound+1))**2
    splitting = []
    used_generators = set()
    for p in range(2, bound+1):
        if not prime(p):
            continue
        roots = [r for r in range(p) if evaluate(f, r) % p == 0]
        if p == 2 and disc == 257:
            assert not roots and p**3 > bound
            splitting.append({"p": p, "splitting_type": "3 (inert)",
                              "prime_ideal_norms": [p**3],
                              "within_bound": False})
            continue
        if p == 2:
            assert disc % 4 == 0 and roots == [1]
            splitting_type = "1^3 (totally ramified)"
            ideal_norms = [2]
        else:
            # Cubic with exactly one simple root: factorization type 1+2.
            assert disc % p != 0 and len(roots) == 1
            splitting_type = "1+2"
            ideal_norms = [p, p*p]
        assert p in generators
        element = generators[p]
        signed_norm = norm(f, element)
        assert abs(signed_norm) == p
        used_generators.add(p)
        splitting.append({"p": p, "splitting_type": splitting_type,
                          "prime_ideal_norms": ideal_norms,
                          "generator_coefficients": element,
                          "generator_signed_norm": signed_norm,
                          "all_relevant_prime_ideals_principal": True,
                          "degree_two_partner":
                          "(p) divided by the principal degree-one prime"
                          if p != 2 else None})
    assert used_generators == set(generators)
    return {"quadratic_discriminant_parameter": d,
            "polynomial_coefficients": f,
            "irreducible_by_rational_root_test": True,
            "totally_real": True, "field_discriminant": disc,
            "maximal_order_certificate": index_certificate,
            "minkowski_bound_floor": bound, "splitting_and_generators": splitting,
            "all_prime_ideals_in_bound_principal": True,
            "class_number": 1}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]
                        / "data" / "cubic_class_number_certificates.json")
    args = parser.parse_args()
    report = {"arithmetic": "exact integers; no floating-point computations",
              "scope": "Finite arithmetic premises of the article's Dedekind-Minkowski proof",
              "fields": [verify_field(d, f, gens) for d, f, gens in FIELDS],
              "all_passed": True}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Five exact cubic class-number certificates passed; {args.output}")


if __name__ == "__main__":
    main()
