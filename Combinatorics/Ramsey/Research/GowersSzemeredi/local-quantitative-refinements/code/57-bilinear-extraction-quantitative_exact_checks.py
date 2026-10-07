#!/usr/bin/env python3
"""Exact finite checks for the quantitative repair of Theorem 13.12.

Only Python's standard library is required. The symbolic exponent comparisons
use integer/rational arithmetic; enormous powers such as 2**(2**70) are never
constructed. Finite examples supplement the written proofs and do not prove
the quantified Fourier, selection, or extraction theorems.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json
from math import factorial, prod
from pathlib import Path


def ceiling(x: F) -> int:
    return -(-x.numerator // x.denominator)


def exponent_checks() -> dict:
    """Recompute every exponent from its preceding interface."""
    first = 1882 + 9312 + 1165
    second = 1882 + 9312 + 1165 * first
    assert (first, second) == (12359, 14409429)

    beta_power = (112 - 15) * 32 + 15
    amplitude_power = 336 * 32
    kernel_constant_power = 44 * 31 + 2 * 31 + 6 * 32
    assert 3**31 * 33**32 <= 2 ** (2 * 31 + 6 * 32)
    assert (beta_power, amplitude_power, kernel_constant_power) == (
        3119, 10752, 1618)
    retained_count_power = beta_power * second + amplitude_power + kernel_constant_power
    density_power = ceiling(F(retained_count_power, 15))
    assert retained_count_power == 44943021421
    assert density_power == 2996201429
    assert 15 * (density_power - 1) < retained_count_power <= 15 * density_power

    # Threshold: 2 beta^-15 [18*33^2/(rho*eta)^2]^32,
    # rho=beta^97*a^336, eta=2^-44, beta>=a^second, a<=1/2.
    assert 18 * 33**2 < 2**17
    threshold_power = 15 * second + 64 * (97 * second + 336) + 1 + 32 * 17 + 64 * 44
    assert threshold_power == 6223 * second + 24865 == 89669901532
    assert threshold_power < 2**37

    # For u=delta^-1>=1, log_2(u)<=2u, and
    # Q(delta)>=2^12*u, so 386+1856 log_2(u)<=2Q(delta).
    assert 2**20 >= 12 and 2**21 >= 1
    assert 386 + 1856 * 2 <= 2 * 2**12

    # Absorb 15*2^(2^20) into a^[-(2^20+4)].
    assert 15 <= 2**4
    inner_length_power = density_power * 2**21 + 2**20 + 4
    square_mass_power = 137 + 704 * density_power
    assert inner_length_power == 6283489820278788 < 2**53
    assert square_mass_power == 2109325806153 < 2**41

    # Printed-exponent overlap. For alpha<=1-2^-10,
    # (2^17-1)log(1/alpha)>log(2). Use log(1/alpha)>=1-alpha
    # and log(2)<3/4, the latter certified by exp(3/4)>65/32>2.
    exponent_ratio_minus_one = 2**70 // 2**53 - 1
    assert exponent_ratio_minus_one == 131071
    assert F(exponent_ratio_minus_one, 2**10) > F(3, 4)
    assert 1 + F(3, 4) + F(3, 4)**2 / 2 == F(65, 32) > 2

    return {
        "first_fibre_density_exponent": first,
        "second_fibre_density_exponent": second,
        "purification_count_exponent": retained_count_power,
        "purification_density_exponent_D": density_power,
        "purification_threshold_exponent": threshold_power,
        "rounded_threshold_exponent": "2^37",
        "inner_length_exponent_before_rounding": inner_length_power,
        "rounded_inner_length_exponent": "2^53",
        "square_mass_exponent_before_rounding": square_mass_power,
        "rounded_square_mass_exponent": "2^41",
        "printed_comparison_factor": exponent_ratio_minus_one,
    }


def endpoint_constant_checks() -> dict:
    # Phase normalization: mean t<=2 eps; character L2^2 error<=2t.
    mean_t = F(2)
    mean_l2_squared = 2 * mean_t
    addition_error = F(3, 2) * 3 * mean_l2_squared
    row_correction = 6
    symmetry_correction = 3
    bilinear_error = addition_error * row_correction * symmetry_correction
    markov_error = mean_t / F(1, 4)
    total_error = bilinear_error + markov_error
    assert addition_error == 18
    assert bilinear_error == 324 and markov_error == 8 and total_error == 332
    epsilon = F(1, 2**10)
    density = 1 - total_error * epsilon
    amplitude = F(3, 4) - 4 * epsilon
    assert density == F(173, 256) > F(1, 2)
    assert amplitude == F(191, 256) > F(1, 2)
    return {
        "separate_addition_error_coefficient": str(addition_error),
        "bilinear_agreement_error_coefficient": str(bilinear_error),
        "total_good_pair_error_coefficient": str(total_error),
        "epsilon_cutoff": str(epsilon),
        "good_pair_density_at_cutoff": str(density),
        "normalized_amplitude_at_cutoff": str(amplitude),
    }


def higher_order_and_cubic_checks() -> dict:
    """Exact new endpoint constants and the demodulating identities."""
    constants = {1: 2}
    for s in range(2, 13):
        constants[s] = 6 + 38 * constants[s - 1]
    for s, value in constants.items():
        assert 37 * value == 80 * 38**(s - 1) - 6
        assert 18 * (12 * s) + 8 == 216 * s + 8
        assert 2 * (216 * s + 8) == 432 * s + 16
    assert 216 * 2 + 8 == 440 > 332

    first_descent = 1 + 18 * 9
    after_normalization = 2 * first_descent
    final_defect = (1 + 2 * 9) * after_normalization
    epsilon_denominator = 6 * 9 * after_normalization
    l2_error = 2 * final_defect + 2
    assert (first_descent, after_normalization, final_defect,
            epsilon_denominator, l2_error) == (163, 326, 6194, 17604, 12390)
    assert final_defect < epsilon_denominator

    # Coefficient-level polynomial identities, not a numerical grid test.
    def sum_of_linear_powers(variables, degree, terms):
        polynomial = Counter()
        for coefficient, indices in terms:
            for monomial_factors in product(indices, repeat=degree):
                exponents = tuple(monomial_factors.count(i) for i in range(variables))
                polynomial[exponents] += coefficient
        return {monomial: coefficient for monomial, coefficient in polynomial.items()
                if coefficient}

    cubic = sum_of_linear_powers(3, 3, ((1, (0, 1, 2)), (-1, (0, 1)),
                                             (-1, (0, 2)), (1, (0,))))
    quadratic = sum_of_linear_powers(2, 2, ((1, (0, 1)), (-1, (0,))))
    assert cubic == {(1, 1, 1): 6, (0, 2, 1): 3, (0, 1, 2): 3}
    assert quadratic == {(1, 1): 2, (0, 2): 1}

    # Independent product and recursive computations of the all-degree
    # descent constants. These exact values are serialized as strings.
    phase_constants = {}
    phase_constant = 2
    for k in range(2, 13):
        if k > 2:
            phase_constant *= 108 * (k - 2) + 1
        direct_product = 2 * prod(108 * r + 1 for r in range(1, k - 1))
        upper_bound = 2 * 109**(k - 2) * factorial(k - 2)
        assert phase_constant == direct_product <= upper_bound
        assert all(108 * r + 1 <= 109 * r for r in range(1, k - 1))
        phase_constants[k] = phase_constant
    assert (phase_constants[2], phase_constants[3], phase_constants[4]) == (
        2, 218, 47306)
    assert final_defect < phase_constants[4]

    # Expand the inclusion-exclusion formula over Z, then compare it with
    # the claimed r-fold difference. This checks coefficients without
    # division in a finite field and includes all lower-degree terms.
    general_difference_checks = []
    for r in range(1, 6):
        terms = []
        for included in product((0, 1), repeat=r):
            indices = (0,) + tuple(i + 1 for i, bit in enumerate(included) if bit)
            terms.append(((-1)**(r - sum(included)), indices))
        difference = sum_of_linear_powers(r + 1, r + 1, terms)
        leading_coefficient = factorial(r + 1)
        expected = {(1,) * (r + 1): leading_coefficient}
        for direction in range(r):
            exponents = [0] + [1] * r
            exponents[direction + 1] += 1
            expected[tuple(exponents)] = leading_coefficient // 2
        assert difference == expected
        general_difference_checks.append({
            "derivative_order": r,
            "polynomial_degree": r + 1,
            "coefficient_of_X_times_direction_product": leading_coefficient,
            "nonzero_monomials": len(difference),
        })

    # Each pair of distinct four-cube vertex forms has an integer minor
    # equal to +1 or -1, hence rank two over every field.
    vertices = list(product((0, 1), repeat=4))
    rank_certificates = 0
    for index, first in enumerate(vertices):
        for second in vertices[index + 1:]:
            coordinate = next(i for i in range(4) if first[i] != second[i])
            determinant = second[coordinate] - first[coordinate]
            assert abs(determinant) == 1
            rank_certificates += 1
    assert rank_certificates == 120
    variance_coefficient = len(vertices)
    defect_taylor_coefficient = F(variance_coefficient, 2)
    assert defect_taylor_coefficient == 8
    assert 1 / defect_taylor_coefficient == F(1, 8)

    # The same integral rank certificate proves pairwise independence for
    # the higher-order sharpness calculation, over every prime field.
    general_cube_checks = []
    for k in range(2, 7):
        cube_vertices = list(product((0, 1), repeat=k))
        pairs = 0
        for index, first in enumerate(cube_vertices):
            for second in cube_vertices[index + 1:]:
                coordinate = next(i for i in range(k) if first[i] != second[i])
                assert abs(second[coordinate] - first[coordinate]) == 1
                pairs += 1
        assert pairs == 2**k * (2**k - 1) // 2
        taylor_coefficient = F(len(cube_vertices), 2)
        assert taylor_coefficient == 2**(k - 1)
        assert 1 / taylor_coefficient == F(1, 2**(k - 1))
        general_cube_checks.append({
            "uniformity_order": k,
            "pair_rank_certificates": pairs,
            "variance_coefficient": len(cube_vertices),
            "distance_to_deficit_limit": str(1 / taylor_coefficient),
        })

    return {
        "general_group_Cs_for_s_1_through_12": {s: str(value) for s, value in constants.items()},
        "cubic_first_descent_factor": first_descent,
        "cubic_normalized_intermediate_defect": after_normalization,
        "cubic_correlation_defect_coefficient": final_defect,
        "cubic_epsilon_strict_denominator": epsilon_denominator,
        "cubic_squared_L2_error_coefficient": l2_error,
        "cubic_identity_nonzero_monomials": {str(k): v for k, v in cubic.items()},
        "quadratic_identity_nonzero_monomials": {str(k): v for k, v in quadratic.items()},
        "all_degree_Kk_for_k_2_through_12": {
            k: str(value) for k, value in phase_constants.items()},
        "all_degree_finite_difference_checks": general_difference_checks,
        "cube_pair_rank_certificates": rank_certificates,
        "sharpness_distance_to_deficit_limit": "1/8",
        "all_degree_sharpness_cube_checks": general_cube_checks,
    }


def kernel_checks() -> dict:
    count = 0
    parameter_cases = []
    for rho, eta in product((F(1), F(1, 2), F(1, 3), F(1, 5)),
                            (F(1), F(1, 2), F(1, 3))):
        length = ceiling(66 / (rho * eta))
        # a=sum_j c_j^32, c_j=(L-|j|)/L^2.
        numerator = length**32 + 2 * sum(j**32 for j in range(1, length))
        a = F(numerator, length**64)
        b = F(1, length**32)
        ratio = a / b
        gamma = rho**32 * eta**31 / (3**31 * 33**32)
        assert length <= 99 / (rho * eta)
        assert ratio >= F(2 * length, 33)
        assert ratio >= 4 / (rho * eta)
        assert rho * a - 2 * b / eta >= rho * a / 2
        assert rho * a / 2 >= gamma
        assert 2 * length**2 <= 18 * 33**2 / (rho * eta)**2
        count += 1
        parameter_cases.append({"rho": str(rho), "eta": str(eta), "L": length})
    return {"exact_parameter_cases": count, "parameters": parameter_cases}


def correction_for_map(values: tuple[int, ...], target: int) -> tuple[int, bool]:
    """Check the BLR correction whenever its exact premise applies."""
    size = len(values)
    failed = sum((values[(x + y) % size] - values[x] - values[y]) % target != 0
                 for x in range(size) for y in range(size))
    if 6 * failed >= size * size:
        return failed, False
    corrected = []
    for x in range(size):
        distribution = Counter((values[(x + y) % size] - values[y]) % target
                               for y in range(size))
        value, multiplicity = distribution.most_common(1)[0]
        assert 2 * multiplicity > size
        # Uniform-in-x majority bound: mass >=1-2 theta.
        assert multiplicity * size >= size * size - 2 * failed
        corrected.append(value)
    assert all((corrected[(x + y) % size] - corrected[x] - corrected[y]) % target == 0
               for x in range(size) for y in range(size))
    distance_count = sum(x != y for x, y in zip(values, corrected))
    theta = F(failed, size * size)
    assert F(distance_count, size) <= theta / (1 - 2 * theta) <= 2 * theta
    return failed, True


def blr_checks() -> dict:
    maps_checked = applicable = nonzero_defect = 0
    for size in range(2, 7):
        for target in (2, 3):
            for values in product(range(target), repeat=size):
                failed, applied = correction_for_map(values, target)
                maps_checked += 1
                applicable += applied
                nonzero_defect += applied and failed > 0
    # Nontrivial near-homomorphisms; small exhaustive groups alone may
    # have no nonzero failure rate below the strict 1/6 threshold.
    for prime in (29, 31):
        for slope, location, error in product((0, 1, 7), (0, 1, prime - 1), (1, 3)):
            values = [(slope * x) % prime for x in range(prime)]
            values[location] = (values[location] + error) % prime
            failed, applied = correction_for_map(tuple(values), prime)
            assert applied and failed > 0
            maps_checked += 1
            applicable += 1
            nonzero_defect += 1
    return {"maps_checked": maps_checked,
            "maps_satisfying_strict_blr_premise": applicable,
            "applicable_maps_with_nonzero_defect": nonzero_defect}


def symmetry_checks() -> dict:
    checked = 0
    for prime in (2, 3, 5):
        for tail in product(range(prime), repeat=prime - 1):
            values = (0,) + tail
            slopes = Counter(values[k] * pow(k, -1, prime) % prime
                             for k in range(1, prime))
            c, maximum = slopes.most_common(1)[0]
            disagreement = sum((values[k] * h - values[h] * k) % prime != 0
                               for h in range(prime) for k in range(prime))
            corrected_error = sum((values[k] * h - c * k * h) % prime != 0
                                  for h in range(prime) for k in range(prime))
            assert disagreement == (prime - 1)**2 - sum(v*v for v in slopes.values())
            assert corrected_error == (prime - 1) * ((prime - 1) - maximum)
            assert corrected_error <= disagreement
            checked += 1
    return {"coefficient_maps_checked": checked, "primes": [2, 3, 5]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("quantitative_exact_checks.json"))
    args = parser.parse_args()
    report = {
        "status": "PASS",
        "arithmetic": "exact Python integers and fractions throughout",
        "scope": "Arithmetic certificates and finite checks; not Lean verification or a proof of the infinite families.",
        "exponents": exponent_checks(),
        "endpoint_constants": endpoint_constant_checks(),
        "higher_orders_and_cubic_inverse": higher_order_and_cubic_checks(),
        "fejer_kernels": kernel_checks(),
        "blr_correction": blr_checks(),
        "symmetric_bilinear_correction": symmetry_checks(),
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
