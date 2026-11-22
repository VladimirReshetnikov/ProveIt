#!/usr/bin/env python3
"""Round a rational direction to a rational Euclidean unit vector.

Run the exact regression checks with "python round_witness.py --test".
Example using accuracy 2^-12:
    python round_witness.py -a 12 1/2 1/3 1/6
Place "--" before coordinate lists containing a negative fraction.
Only Python's standard library is needed.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from random import Random


def sign(x):
    return (x > 0) - (x < 0)


def sign_of_radical(constant, coefficient, radicand):
    """Exact sign of constant + coefficient * sqrt(radicand)."""
    if radicand < 0:
        raise ValueError("radicand must be nonnegative")
    if not coefficient or not radicand:
        return sign(constant)
    if not constant or sign(constant) == sign(coefficient):
        return sign(coefficient)
    return sign(constant) * sign(constant**2 - coefficient**2 * radicand)


def direction_error_at_most(p, z, delta):
    """Test ||z - p/sqrt(p·p)||_1 <= delta, with exact rational arithmetic."""
    if len(p) != len(z) or not any(p):
        raise ValueError("expected a nonzero direction and equally many coordinates")
    radicand = sum(x**2 for x in p)
    # For rho = sqrt(radicand), assign the sign of rho*z_i - p_i.
    signs = [sign_of_radical(-x, y, radicand) for x, y in zip(p, z)]
    signed_p = sum(s * x for s, x in zip(signs, p))
    signed_z = sum(s * y for s, y in zip(signs, z))
    # Multiplying the distance test by rho gives
    # signed_p + (delta - signed_z)*rho >= 0.
    return sign_of_radical(signed_p, delta - signed_z, radicand) >= 0


@dataclass(frozen=True)
class RoundWitness:
    point: tuple
    chart_axis: int
    chart_scale: int
    common_denominator: int


def round_witness(direction, accuracy):
    """For ||p||_1 = 1 return a rational unit z within 2^-accuracy of its ray."""
    p = tuple(Q(x) for x in direction)
    if not p or sum(abs(x) for x in p) != 1:
        raise ValueError("the direction must have l1 norm one")
    if not isinstance(accuracy, int) or accuracy < 0:
        raise ValueError("accuracy must be a natural-number exponent")

    d = len(p)
    axis = max(range(d), key=lambda j: abs(p[j]))  # first maximum wins
    q = abs(p[axis])
    factor = 2 * d * (d**2 + d)
    steps = accuracy + (factor - 1).bit_length()  # ceiling of log2(factor)
    scale = 2**steps
    radicand = sum(x**2 for x in p)
    low, high = Q(0), Q(1)
    for _ in range(steps):
        mid = (low + high) / 2
        if mid * mid < radicand:
            low = mid
        else:
            high = mid

    # int(Fraction) truncates toward zero, including for negative coordinates.
    others = [j for j in range(d) if j != axis]
    grid = {j: int(scale * p[j] / (high + q)) for j in others}
    grid_sq = sum(m**2 for m in grid.values())
    denominator = scale**2 + grid_sq
    z = [Q(0)] * d
    z[axis] = Q(sign(p[axis]) * (scale**2 - grid_sq), denominator)
    for j in others:
        z[j] = Q(2 * grid[j] * scale, denominator)

    assert sum(y**2 for y in z) == 1
    assert denominator <= 2 * scale**2
    tolerance = Q(1, 2**accuracy)
    assert direction_error_at_most(p, z, tolerance)
    l1_norm = sum(abs(y) for y in z)
    assert sum(abs(y / l1_norm - x) for x, y in zip(p, z)) <= 2 * tolerance
    return RoundWitness(tuple(z), axis, scale, denominator)


def self_test():
    checked = 0
    for p in [(Q(1),), (Q(-1),)]:
        assert round_witness(p, 7).point == p
        checked += 1

    equator = (Q(3, 7), Q(-4, 7), Q(0))
    nonsquare = (Q(1, 2), Q(1, 3), Q(1, 6))
    assert sum(x**2 for x in nonsquare) == Q(7, 18)
    for a in (0, 1, 8, 25):
        assert round_witness(equator, a).point[2] == 0
        round_witness(nonsquare, a)
        tie = round_witness((Q(-1, 2), Q(1, 2), Q(0)), a)
        assert tie.chart_axis == 0 and tie.point[0] < 0
        checked += 3

    # This exact irrational direction has l1 distance exactly 1 from (1,0).
    p = (Q(1, 2), Q(1, 2))
    assert direction_error_at_most(p, (Q(1), Q(0)), Q(1))
    assert not direction_error_at_most(p, (Q(1), Q(0)), Q(999, 1000))

    rng = Random(1009)
    for d in range(2, 7):
        for a in (0, 3, 9, 18):
            for _ in range(3):
                ray = [rng.randint(-7, 7) for _ in range(d)]
                if not any(ray):
                    ray[0] = 1
                total = sum(abs(x) for x in ray)
                round_witness([Q(x, total) for x in ray], a)
                checked += 1
    print(f"Passed exact sphere, denominator, and error checks for {checked} witnesses.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-a", "--accuracy", type=int, default=10)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("coordinates", nargs="*", type=Q)
    args = parser.parse_args()
    if args.test:
        self_test()
    elif args.coordinates:
        result = round_witness(args.coordinates, args.accuracy)
        print("point =", tuple(str(x) for x in result.point))
        print("chart grid scale =", result.chart_scale)
        print("common denominator =", result.common_denominator)
        print(f"verified l1 error <= 2^-{args.accuracy}")
    else:
        parser.error("supply rational coordinates or pass --test")
