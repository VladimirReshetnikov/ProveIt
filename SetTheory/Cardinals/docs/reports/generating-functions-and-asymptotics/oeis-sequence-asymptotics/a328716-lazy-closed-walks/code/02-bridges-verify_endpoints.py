#!/usr/bin/env python3
"""Exact prescribed-endpoint certificate, using only the standard library.

Compares the normalized Bessel coefficient/prefactor formula against direct
dynamic enumeration of weighted endpoints. All arithmetic is rational.
The fixed grid contains 1,303 comparisons, including zero activities,
one-sided axes, N < |x|_1, and a zero residual paired-step budget.

Run with: python verify_endpoints.py
Checks remain active under python -O.
"""

from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import factorial


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def coefficient_count(length, endpoint, activities, idle):
    """Compute P[N,x] [t^m] H_ep(idle^2 t) prod_i F_|x_i|(a_i b_i t).

    F_nu(t) = nu! sum_k t^k / (k! (k+nu)!).
    P[N,x] = N! idle^ep prod_i a_i^x_i^+ b_i^x_i^- / |x_i|!.
    length - |endpoint|_1 = 2m + ep.
    """
    idle = Fraction(idle)
    activities = [(Fraction(a), Fraction(b)) for a, b in activities]
    displacement = sum(map(abs, endpoint))
    if length < displacement:
        return Fraction(0)
    paired_budget, parity = divmod(length-displacement, 2)
    prefactor = Fraction(factorial(length)) * idle**parity
    coefficient = [
        idle**(2*k) / factorial(2*k+parity)
        for k in range(paired_budget+1)
    ]
    for coordinate, (positive, negative) in zip(endpoint, activities):
        order = abs(coordinate)
        prefactor *= (
            positive**max(coordinate, 0)
            * negative**max(-coordinate, 0)
            / factorial(order)
        )
        factor = [
            Fraction(factorial(order)) * (positive*negative)**k
            / (factorial(k)*factorial(k+order))
            for k in range(paired_budget+1)
        ]
        coefficient = [
            sum(
                (coefficient[j]*factor[k-j] for j in range(k+1)),
                Fraction(0),
            )
            for k in range(paired_budget+1)
        ]
    return prefactor*coefficient[paired_budget]


def weighted_increments(activities, idle):
    """Construct literal step vectors and activities for direct enumeration."""
    dimension = len(activities)
    origin = (0,)*dimension
    increments = [(origin, Fraction(idle))]
    for axis, (positive, negative) in enumerate(activities):
        for sign, weight in [(1, positive), (-1, negative)]:
            vector = tuple(
                sign if index == axis else 0
                for index in range(dimension)
            )
            increments.append((vector, Fraction(weight)))
    return increments


def next_endpoint_distribution(states, increments):
    """Take one weighted walk step; this uses no coefficient formula."""
    following = defaultdict(Fraction)
    for endpoint, mass in states.items():
        for shift, activity in increments:
            if activity:
                destination = tuple(
                    coordinate+step for coordinate, step in zip(endpoint, shift)
                )
                following[destination] += mass*activity
    return following


def main():
    rational = Fraction
    cases = [
        ([], rational(2, 3)),
        ([], rational(0)),
        ([(rational(2), rational(3))], rational(1, 2)),
        ([(rational(0), rational(3))], rational(0)),
        ([(rational(0), rational(3))], rational(2)),
        (
            [(rational(2), rational(3)), (rational(4), rational(5))],
            rational(1, 2),
        ),
        (
            [(rational(0), rational(3)), (rational(4), rational(0))],
            rational(0),
        ),
        (
            [(rational(0), rational(3)), (rational(4), rational(5))],
            rational(0),
        ),
    ]
    comparisons = 0
    for activities, idle in cases:
        dimension = len(activities)
        origin = (0,)*dimension
        increments = weighted_increments(activities, idle)
        states = {origin: rational(1)}
        for length in range(7):
            # Include every reached endpoint and a cube containing impossible
            # endpoints, so inaccessible and zero-prefactor cases are tested.
            targets = set(states) | set(product(range(-3, 4), repeat=dimension))
            for endpoint in targets:
                expected = states.get(endpoint, rational(0))
                actual = coefficient_count(length, endpoint, activities, idle)
                require(
                    actual == expected,
                    "Endpoint mismatch: "
                    f"N={length}, x={endpoint}, activities={activities}, "
                    f"idle={idle}, coefficient={actual}, DP={expected}",
                )
                comparisons += 1
            states = next_endpoint_distribution(states, increments)
    require(comparisons == 1303, f"Unexpected comparison count: {comparisons}")
    print("Exact prescribed-endpoint comparisons passed:", comparisons)
    print(
        "Coverage: dimensions 0, 1, 2; lengths 0 through 6; eight activity "
        "models; rational asymmetric and one-sided directional activities; "
        "positive and zero idle activity."
    )
    print(
        "Every reached endpoint plus the cube {-3,...,3}^D is compared at "
        "each length, including N < |x|_1, m=0, zero prefactors, constant "
        "generators, and nonzero endpoints."
    )


if __name__ == "__main__":
    main()
