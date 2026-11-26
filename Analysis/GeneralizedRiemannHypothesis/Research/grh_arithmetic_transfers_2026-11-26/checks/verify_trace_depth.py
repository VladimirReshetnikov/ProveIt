#!/usr/bin/env python3
"""Exact checks for the report's cyclic intertwiner model.

This is a finite algebra certificate, not a Lean proof or a Galois realization.
Requires Python >=3.10 and SymPy. Writes a JSON summary to stdout or --output.
"""
from __future__ import annotations

import argparse
import itertools
import json
from math import comb, gcd
from pathlib import Path

from sympy import Matrix, ZZ, eye
from sympy.matrices.normalforms import smith_normal_form


def flattened(matrix):
    return [int(matrix[i, j]) for i in range(matrix.rows) for j in range(matrix.cols)]


def relation_matrix(pairs):
    """Integer coefficient matrix for X*rho(g)-sigma(g)*X=0."""
    d = pairs[0][0].rows
    units = []
    for i in range(d):
        for j in range(d):
            unit = Matrix.zeros(d, d)
            unit[i, j] = 1
            units.append(unit)
    blocks = []
    for rho_g, sigma_g in pairs:
        blocks.append(Matrix.hstack(*[Matrix(flattened(x * rho_g - sigma_g * x)) for x in units]))
    return Matrix.vstack(*blocks)


def valuation(number, p):
    if number == 0:
        return None
    result = 0
    number = abs(number)
    while number % p == 0:
        result += 1
        number //= p
    return result


def brute_kernel_count(relations, modulus):
    rows = [[int(x) for x in row] for row in relations.tolist()]
    return sum(
        all(sum(a * b for a, b in zip(row, vector)) % modulus == 0 for row in rows)
        for vector in itertools.product(range(modulus), repeat=relations.cols)
    )


def tau_coefficients(limit):
    """Compute q*product(1-q^m)^24 exactly through q^limit."""
    poly = [1] + [0] * (limit - 1)
    for m in range(1, limit):
        new = [0] * limit
        for i, value in enumerate(poly):
            for r in range(min(24, (limit - 1 - i) // m) + 1):
                new[i + r * m] += value * (-1)**r * comb(24, r)
        poly = new
    return [0] + poly


def predicted_tate_depth(ell, j):
    M = 10 + 2 * j
    if M == 0:
        return None  # infinity
    if M % (ell - 1):
        return 0
    return 1 + valuation(M, ell)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    A = Matrix([[1, 1], [0, 1]])
    B = Matrix([[1, 0], [1, 1]])
    basis = [eye(2), A, B, A * B]
    basis_det = int(Matrix.hstack(*[Matrix(flattened(g)) for g in basis]).det())
    gram_det = int(Matrix([[int((g * h).trace()) for h in basis] for g in basis]).det())
    assert abs(basis_det) == abs(gram_det) == 1
    result = {
        "status": "all exact checks passed",
        "meaning": "finite algebra model; not an arithmetic or Lean certification",
        "basis_determinant": basis_det,
        "trace_gram_determinant": gram_det,
        "cases": [],
    }
    for p, depth in [(2, 1), (2, 3), (3, 2), (5, 1)]:
        q = 1 + p**depth
        relations = relation_matrix([(A, A), (B, B), (eye(2), q * eye(2))])
        snf = smith_normal_form(relations, domain=ZZ)
        factors = [abs(int(snf[i, i])) for i in range(4)]
        assert factors == [1, 1, 1, p**depth], (p, depth, factors)
        trace_discrepancies = [(1 - q) * int(g.trace()) for g in basis]
        detected_depth = min(v for x in trace_discrepancies if (v := valuation(x, p)) is not None)
        assert detected_depth == depth
        # Full exhaustive matrix enumeration, independent of the scalar-kernel formula.
        brute = []
        bound = 4 if p == 2 else 2
        for n in range(1, bound + 1):
            count = brute_kernel_count(relations, p**n)
            expected = p ** min(n, depth)
            assert count == expected, (p, depth, n, count, expected)
            brute.append({"n": n, "modulus": p**n, "kernel_size": count, "length": min(n, depth)})
        result["cases"].append({
            "p": p, "depth": depth, "q": q,
            "relation_matrix": [[int(x) for x in row] for row in relations.tolist()],
            "smith_factors": factors,
            "scalar_trace_discrepancy": trace_discrepancies[0],
            "scalar_trace_valuation": valuation(trace_discrepancies[0], p),
            "trace_discrepancies_z_times_1_x_y_xy": trace_discrepancies,
            "minimum_trace_discrepancy_valuation": detected_depth,
            "exhaustive_kernel_checks": brute,
            "kernel_length_all_n_proved_by_smith_form": "min(n,depth)",
            "source_style_scalar_upper_bound": 2 * depth,
            "sharp_scalar_upper_bound": depth,
        })
    # At p=2 a transpose scalar need not be +1 or -1 modulo 8.
    exotic = []
    for epsilon in (1, 3, 5, 7):
        P = Matrix([[0, 1], [epsilon, 0]])
        assert all(int(x) % 8 == 0 for x in P.T - epsilon * P)
        symmetric_scalars = [b for b in range(8) if all(int(x) % 8 == 0 for x in b * (P.T - P))]
        expected = 2 ** min(3, valuation(epsilon - 1, 2) if epsilon != 1 else 3)
        assert len(symmetric_scalars) == expected
        exotic.append({"epsilon_mod_8": epsilon, "matrix": [[int(x) for x in row] for row in P.tolist()], "symmetric_scalar_count": len(symmetric_scalars)})
    result["dyadic_transpose_scalars"] = exotic
    # Actual arithmetic numerator data for the Ramanujan example. The Galois
    # image theorem is a cited mathematical input, not proved by this check.
    taus = tau_coefficients(3)
    assert taus == [0, 1, -24, 252]
    delta_d2 = abs(taus[2]) * (2**10 - 1)
    delta_d3 = abs(taus[3]) * (3**10 - 1)
    assert (delta_d2, delta_d3, gcd(delta_d2, delta_d3)) == (24552, 14880096, 792)
    assert valuation(delta_d2, 11) == 1 and valuation(delta_d3, 11) == 2
    assert (-23) % 8 == 1 and (-23) % 3 == 1
    result["ramanujan_global_term_certificate"] = {
        "CM_field_discriminant": -23,
        "tau_coefficients_computed_from_product_through_3": taus,
        "test_primes_split_in_CM_field": [2, 3],
        "absolute_trace_discrepancy_numerators": [delta_d2, delta_d3],
        "gcd": 792,
        "gcd_factorization": {"2": 3, "3": 2, "11": 1},
        "excluded_exceptional_primes": [2, 3, 5, 7, 23, 691],
        "theorem_using_classical_image_result": "C_11=1; C_ell=0 at all other nonexceptional ell",
        "not_certified_by_this_computation": ["Galois image theorem", "full SelmerDatum hypotheses"],
    }
    # Check every unit in several finite cyclotomic image groups. This verifies
    # the local depth formula numerically at these levels; the report proves it
    # for all ell,j,n using the unit decomposition and lifting the exponent.
    tate_checks = []
    tate_weights = [-5, -1, 0, 1, 2, 3, 4, 50, 73, 131, 166, 600]
    for ell in [11, 13, 17, 19]:
        for j in tate_weights:
            M = 10 + 2 * j
            predicted = predicted_tate_depth(ell, j)
            for n in range(1, 4):
                modulus = ell**n
                depth = min(
                    n if (x := pow(u, M, modulus) - 1) == 0 else valuation(x, ell)
                    for u in range(1, modulus) if u % ell
                )
                assert depth == (n if predicted is None else min(n, predicted))
            tate_checks.append({"ell": ell, "j": j, "M": M, "depth": "infinity" if predicted is None else predicted,
                                "all_units_checked_at_levels": [1, 2, 3]})
    result["tate_twist_cyclotomic_unit_checks"] = tate_checks
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
