"""Certified intrinsic eccentricity and diameter bounds for rational side lengths.

Run beside hyperbox.py. The mesh parameter m is the number of equal
subintervals on every axis. Coordinates and squared distances are exact.
"""

import argparse
from fractions import Fraction
from itertools import product
import json
from math import isqrt

from hyperbox import surface_squared


def sqrt_bracket(square, bits):
    """Enclose the nonnegative square root by consecutive dyadics, or exactly."""
    scale = 1 << bits
    scaled = square * scale * scale
    root = isqrt(scaled.numerator // scaled.denominator)
    lo = Fraction(root, scale)
    if lo * lo == square:
        return lo, lo
    return lo, Fraction(root + 1, scale)


def boundary_indices(dimension, m):
    for indices in product(range(m + 1), repeat=dimension):
        if 0 in indices or m in indices:
            yield indices


def encode_point(point):
    return [str(coordinate) for coordinate in point]


def best_record(winner, endpoint_count, rho_square, global_upper_square, bits):
    square, p, q = winner
    lo, hi = sqrt_bracket(square, bits)
    _, rho_hi = sqrt_bracket(rho_square, bits)
    _, global_hi = sqrt_bracket(global_upper_square, bits)
    return {
        "witness": [encode_point(p), encode_point(q)],
        "witness_distance_squared": str(square),
        "certified_length_interval": [str(lo), str(min(hi + endpoint_count * rho_hi, global_hi))],
        "exact_interval_formula": {
            "lower": f"sqrt({square})",
            "upper": (f"min(sqrt({global_upper_square}), sqrt({square})"
                      f" + {endpoint_count}*sqrt({rho_square}))"),
        },
    }


def certify(sides, m=2, bits=32, fixed_only=False, vertex=None):
    sides = tuple(map(Fraction, sides))
    n = len(sides)
    if n < 2 or min(sides) <= 0 or m < 1 or bits < 0:
        raise ValueError("at least two positive sides, m >= 1, and bits >= 0 required")
    vertex = tuple(0 for _ in sides) if vertex is None else tuple(vertex)
    if len(vertex) != n or any(bit not in (0, 1) for bit in vertex):
        raise ValueError("vertex must contain one bit for each axis")

    grid = [(indices, tuple(length * i / m for length, i in zip(sides, indices)))
            for indices in boundary_indices(n, m)]
    zero = tuple(Fraction(0) for _ in sides)
    fixed = (Fraction(0), zero, zero)
    free = fixed
    calls = 0

    # Every first endpoint can be reflected into the lower half of each
    # axis while preserving the grid. Keep all second endpoints.
    for indices, p in grid:
        if fixed_only and p != zero:
            continue
        if any(2 * index > m for index in indices):
            continue
        for _, q in grid:
            square = surface_squared(sides, p, q)
            calls += 1
            if p == zero and square > fixed[0]:
                fixed = square, p, q
            if square > free[0]:
                free = square, p, q

    # Nearest rounding preserves any incident facet, and changes each of
    # the n-1 free coordinates k by at most sides[k]/(2*m).
    squares = [length * length for length in sides]
    rho_square = (sum(squares) - min(squares)) / (4 * m * m)
    ordered = sorted(sides)
    upper_square = sum(squares) + 2 * ordered[-2] * ordered[-1]

    def reflect(point):
        return tuple(a - x if bit else x for bit, a, x in zip(vertex, sides, point))

    fixed_square, p, q = fixed
    output = {
        "sides": encode_point(sides),
        "mesh_subdivisions": m,
        "distance_oracle_calls": calls,
        "rounding_radius_squared": str(rho_square),
        "fixed": best_record((fixed_square, reflect(p), reflect(q)), 1,
                             rho_square, upper_square, bits),
    }
    if not fixed_only:
        output["free"] = best_record(free, 2, rho_square, upper_square, bits)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sides", help="comma-separated integers or fractions")
    parser.add_argument("--m", type=int, default=2, help="subintervals per axis")
    parser.add_argument("--bits", type=int, default=32, help="dyadic precision of bounds")
    parser.add_argument("--fixed-only", action="store_true")
    parser.add_argument("--vertex", help="comma-separated corner bits for the fixed calculation")
    args = parser.parse_args()
    vertex = None if args.vertex is None else [int(x) for x in args.vertex.split(",")]
    print(json.dumps(certify(args.sides.split(","), args.m, args.bits,
                             args.fixed_only, vertex), indent=2))


if __name__ == "__main__":
    main()
