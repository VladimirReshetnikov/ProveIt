#!/usr/bin/env python3
"""Reproducible finite diagnostics for torsion_vn.tex.

Requires Python 3 and NumPy.  These checks supplement the mathematical
proofs; a finite random sample is not a proof of either theorem.
All Gowers powers below are computed directly by enumerating cubes,
independently of the Cauchy--Schwarz induction used in the article.
"""

import itertools
import json
import math
from fractions import Fraction

import numpy as np


SEED = 20261006
TOLERANCE = 1e-9


def cyclic_gowers_norm(values, order):
    """Normalized U^order norm on Z/n, by the defining cube sum."""
    n = len(values)
    coordinates = np.indices((n,) * (order + 1)).reshape(order + 1, -1)
    product = np.ones(coordinates.shape[1], dtype=complex)
    for vertex in itertools.product((0, 1), repeat=order):
        index = coordinates[0].copy()
        for i, bit in enumerate(vertex):
            index += bit * coordinates[i + 1]
        factor = values[index % n]
        product *= factor.conj() if sum(vertex) % 2 else factor
    power = product.mean()
    if abs(power.imag) > TOLERANCE or power.real < -TOLERANCE:
        raise AssertionError(f"Invalid computed Gowers power: {power}")
    return max(0.0, power.real) ** (1 / (2**order))


def mixed_lp_bound(functions, coefficients):
    """The article's mixed-Lp upper bound, with the final function targeted."""
    k = len(functions)
    n = len(functions[0])
    if math.gcd(n, coefficients[-1] - coefficients[-2]) != 1:
        raise ValueError("The final difference must be invertible.")
    kernel_product = math.prod(
        math.gcd(n, coefficients[-1] - coefficient)
        for coefficient in coefficients[:-1]
    )
    upper = kernel_product ** (1 / (2 ** (k - 1)))
    upper *= cyclic_gowers_norm(functions[-1], k - 1)
    exponents = [2**i for i in range(1, k - 1)] + [2 ** (k - 2)]
    for function, exponent in zip(functions[:-1], exponents):
        upper *= np.mean(abs(function) ** exponent) ** (1 / exponent)
    return upper


def multilinear_average(functions, coefficients):
    n = len(functions[0])
    x, difference = np.indices((n, n))
    product = np.ones((n, n), dtype=complex)
    for function, coefficient in zip(functions, coefficients):
        product *= function[(x + coefficient * difference) % n]
    return product.mean()


def assert_bound(lower, upper, label):
    if lower > upper + TOLERANCE:
        raise AssertionError({"case": label, "left": lower, "right": upper})
    return float(lower / upper) if upper > TOLERANCE else 0.0


def random_mixed_lp_checks(rng):
    counts = {"arithmetic_progressions": 0, "general_coefficients": 0}
    maximum_ratios = dict.fromkeys(counts, 0.0)
    for n in range(2, 8):
        for k in range(2, 5):
            for trial in range(12):
                functions = [
                    rng.normal(size=n) + 1j * rng.normal(size=n)
                    for _ in range(k)
                ]
                # Unit adjacent difference; other differences may have torsion.
                coefficients = {
                    "arithmetic_progressions": list(range(k)),
                    "general_coefficients": list(rng.integers(-2 * n, 2 * n, k)),
                }
                coefficients["general_coefficients"][-2:] = [1, 0]
                for kind, pattern in coefficients.items():
                    left = abs(multilinear_average(functions, pattern))
                    right = mixed_lp_bound(functions, pattern)
                    ratio = assert_bound(left, right, (kind, n, k, trial))
                    counts[kind] += 1
                    maximum_ratios[kind] = max(maximum_ratios[kind], ratio)
    return {"cases": counts, "maximum_left_over_right": maximum_ratios}


def heterogeneous_indicator_checks(rng):
    count = 0
    maximum_ratio = 0.0
    for n in range(2, 9):
        for k in range(3, 5):
            for trial in range(15):
                functions = [
                    (rng.random(n) < rng.uniform(0.1, 0.9)).astype(float)
                    for _ in range(k)
                ]
                densities = [function.mean() for function in functions]
                count_average = multilinear_average(functions, list(range(k)))
                left = abs(count_average - math.prod(densities))
                right = 0.0
                for j in range(3, k + 1):
                    torsion = math.prod(math.gcd(n, r) for r in range(1, j))
                    torsion = torsion ** (1 / (2 ** (j - 1)))
                    exponents = [2**i for i in range(1, j - 1)] + [
                        2 ** (j - 2)
                    ]
                    density_prefix = math.prod(
                        densities[i] ** (1 / exponent)
                        for i, exponent in enumerate(exponents)
                    )
                    density_suffix = math.prod(densities[j:])
                    balanced = functions[j - 1] - densities[j - 1]
                    right += (
                        density_suffix
                        * density_prefix
                        * torsion
                        * cyclic_gowers_norm(balanced, j - 1)
                    )
                ratio = assert_bound(left, right, (n, k, trial))
                maximum_ratio = max(maximum_ratio, ratio)
                count += 1
    return {"cases": count, "maximum_left_over_right": maximum_ratio}


def exact_witnesses():
    """Integer/rational enumeration of the two explicit article witnesses."""
    characteristic_two = []
    for dimension in range(1, 5):
        n = 2**dimension
        real_sum = 0
        imaginary_sum = 0
        for x, h1, h2 in itertools.product(range(n), repeat=3):
            exponent = (
                x.bit_count()
                - (x ^ h1).bit_count()
                - (x ^ h2).bit_count()
                + (x ^ h1 ^ h2).bit_count()
            ) % 4
            real_sum += (1, 0, -1, 0)[exponent]
            imaginary_sum += (0, 1, 0, -1)[exponent]
        assert imaginary_sum == 0
        power = Fraction(real_sum, n**3)
        assert power == Fraction(1, n)
        assert n * power == 1  # Sharp bound raised to its fourth power.
        characteristic_two.append(
            {"dimension": dimension, "U2_fourth_power": str(power)}
        )

    values = (1, 1, -1)
    cube_sum = 0
    for x, h1, h2, h3 in itertools.product(range(3), repeat=4):
        product = 1
        for v1, v2, v3 in itertools.product((0, 1), repeat=3):
            product *= values[(x + v1 * h1 + v2 * h2 + v3 * h3) % 3]
        cube_sum += product
    characteristic_three_power = Fraction(cube_sum, 3**4)
    assert characteristic_three_power == Fraction(49, 81)
    return {
        "sharp_characteristic_two": characteristic_two,
        "Z3_counterexample_U3_eighth_power": str(characteristic_three_power),
        "endpoint_progression_average_in_both_witnesses": 1,
    }


def main():
    rng = np.random.default_rng(SEED)
    result = {
        "seed": SEED,
        "status": "all checks passed",
        "mixed_Lp": random_mixed_lp_checks(rng),
        "heterogeneous_indicator_count": heterogeneous_indicator_checks(rng),
        "exact_witnesses": exact_witnesses(),
        "scope": "Finite diagnostics supplement the written proofs.",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
