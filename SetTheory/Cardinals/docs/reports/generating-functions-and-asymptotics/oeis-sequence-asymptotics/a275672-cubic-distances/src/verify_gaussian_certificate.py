#!/usr/bin/env python3
"""Exact integer verifier for the four-node Gaussian upper-bound certificate.

No floating-point operations enter any assertion. Decimal output is for display.
The proof uses exp(-x) Taylor brackets after division of x by 16, followed by
four directed squarings. All kernel arguments are 10*(d/10000)**2.
"""

from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path


SCALE = 10**40
GRID = 10_000
NODES = (0, 3791, 6209, 10_000)
WEIGHTS = (3183, 1817, 1817, 3183)
WEIGHT_DENOMINATOR = 10_000
LAMBDA = 10
TAYLOR_DEGREE = 21


def ceil_div(a, b):
    return -((-a) // b)


def exponential_interval(d):
    """Integers lo,hi with lo/SCALE <= exp(-10*(d/GRID)^2) <= hi/SCALE."""
    # y = x/16 = d^2 / 160000000 belongs to [0,5/8].
    numerator = d * d
    denominator = 16 * GRID * GRID // LAMBDA
    assert 0 <= 8 * numerator <= 5 * denominator
    power_numerator = 1
    power_denominator = 1
    factorial = 1
    lower = 0
    upper = 0
    for k in range(TAYLOR_DEGREE + 1):
        if k:
            power_numerator *= numerator
            power_denominator *= denominator
            factorial *= k
        term_numerator = SCALE * power_numerator
        term_denominator = power_denominator * factorial
        term_lo, rem = divmod(term_numerator, term_denominator)
        term_hi = term_lo + bool(rem)
        if k % 2:
            lower -= term_hi
            if k <= TAYLOR_DEGREE - 1:
                upper -= term_lo
        else:
            lower += term_lo
            if k <= TAYLOR_DEGREE - 1:
                upper += term_hi
    # Odd Taylor sum S_21 <= exp(-y) <= S_20; arithmetic was outward rounded.
    assert 0 < lower <= upper <= SCALE
    for _ in range(4):
        lower = lower * lower // SCALE
        upper = ceil_div(upper * upper, SCALE)
    return lower, upper


def display(q, digits=35):
    with localcontext() as context:
        context.prec = digits
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def main():
    intervals = [exponential_interval(d) for d in range(GRID + 1)]
    min_numerator = None
    min_index = None
    # Symmetry about 1/2 permits checking one half of the mesh.
    for i in range(GRID // 2 + 1):
        potential_lo = sum(
            w * intervals[abs(i - x)][0]
            for w, x in zip(WEIGHTS, NODES)
        )
        if min_numerator is None or potential_lo < min_numerator:
            min_numerator = potential_lo
            min_index = i
    mesh_lower = Fraction(min_numerator, WEIGHT_DENOMINATOR * SCALE)
    # |U''| <= 2*lambda = 20, so linear interpolation loses <=20*h^2/8.
    interpolation_error = Fraction(2 * LAMBDA, 8 * GRID * GRID)
    global_lower = mesh_lower - interpolation_error
    chosen_lower = Fraction(36_532_567, 100_000_000)
    assert global_lower >= chosen_lower

    energy_upper = Fraction(
        sum(
            wa * wb * intervals[abs(xa - xb)][1]
            for wa, xa in zip(WEIGHTS, NODES)
            for wb, xb in zip(WEIGHTS, NODES)
        ),
        WEIGHT_DENOMINATOR**2 * SCALE,
    )
    chosen_energy_upper = Fraction(36_533_029, 100_000_000)
    assert energy_upper <= chosen_energy_upper
    kappa = 2 * chosen_lower**3 - chosen_energy_upper**3
    assert kappa > 0
    # Dropping exp(-30) only enlarges the distance-Laplace upper bound.
    constant_squared = Fraction(1, 6) / kappa
    assert constant_squared < Fraction(1849, 1000) ** 2
    assert constant_squared < Fraction(37, 20) ** 2

    with localcontext() as context:
        context.prec = 35
        constant = (
            Decimal(constant_squared.numerator)
            / Decimal(constant_squared.denominator)
        ).sqrt()

    result = {
        "status": "VERIFIED_EXACT_INTEGER_ARITHMETIC",
        "kernel_lambda": LAMBDA,
        "node_numerators": NODES,
        "node_denominator": GRID,
        "weight_numerators": WEIGHTS,
        "weight_denominator": WEIGHT_DENOMINATOR,
        "mesh_denominator": GRID,
        "taylor_odd_degree": TAYLOR_DEGREE,
        "fixed_point_scale": str(SCALE),
        "minimum_mesh_index_half_interval": min_index,
        "mesh_potential_lower_decimal": display(mesh_lower),
        "interpolation_error": str(interpolation_error),
        "global_potential_lower_decimal": display(global_lower),
        "certified_potential_lower": str(chosen_lower),
        "computed_energy_upper_decimal": display(energy_upper),
        "certified_energy_upper": str(chosen_energy_upper),
        "kappa_exact": str(kappa),
        "kappa_decimal": display(kappa),
        "constant_squared_exact": str(constant_squared),
        "constant_decimal": str(constant),
        "strict_rational_bound": "1849/1000",
        "claim": "limsup a_n/n <= sqrt(1/(6*kappa)) < 1.849",
    }
    target = Path(__file__).with_name("gaussian_certificate_verified.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
