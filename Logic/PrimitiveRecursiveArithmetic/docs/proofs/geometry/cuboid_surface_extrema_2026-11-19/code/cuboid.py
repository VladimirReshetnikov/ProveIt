#!/usr/bin/env python3
"""Intrinsic extremal distances of a positive rectangular cuboid.

Only Python's standard library is required. Formula evaluations use Decimal;
the non-elementary branch is solved by a monotone, bracketed scalar equation,
not by optimization over a mesh. See ../cuboid_surface.tex for the proof.

The returned root bracket is a high-precision numerical check, not an interval
arithmetic certificate. Near an exact transition the supplied decimal sides
are the inputs, rather than an unstated symbolic interpretation of them.
"""

import argparse
from decimal import Decimal, localcontext
import json


def positive_sqrt(x):
    return max(Decimal(0), x).sqrt()


def antipodal_squared_distances(a, b, c, x, y):
    """Five unfolding lengths squared, in sorted coordinates."""
    return [
        (a + c) ** 2 + (b - 2 * y) ** 2,
        (b + c) ** 2 + (a - 2 * x) ** 2,
        (c + x + y) ** 2 + (a + b - x - y) ** 2,
        (a + b) ** 2 + (c + 2 * y) ** 2,
        (a + b) ** 2 + (c + 2 * x) ** 2,
    ]


def vertex_face_squared_distances(a, b, c, x, y):
    """Four source-image lengths squared to (x,y,c)."""
    return [
        (c + x) ** 2 + y ** 2,
        x ** 2 + (c + y) ** 2,
        (a + c - x) ** 2 + (a + y) ** 2,
        (b + x) ** 2 + (b + c - y) ** 2,
    ]


def solve(side_a, side_b, side_c, precision=70):
    """Return formula values and witnesses, mapped to the input axis order.

    A selected vertex other than the origin is handled by reflecting each
    coordinate i for which that vertex has coordinate side_i.
    """
    with localcontext() as ctx:
        ctx.prec = precision
        sides = [Decimal(str(t)) for t in (side_a, side_b, side_c)]
        if not all(t.is_finite() and t > 0 for t in sides):
            raise ValueError("All three side lengths must be finite and positive")
        order = sorted(range(3), key=lambda i: sides[i])
        a, b, c = [sides[i] for i in order]

        def original(p):
            q = [Decimal(0)] * 3
            for i, value in zip(order, p):
                q[i] = value
            return q

        def f(q):
            return (positive_sqrt(q - (a + c) ** 2)
                    + positive_sqrt(q - (b + c) ** 2)
                    + positive_sqrt(2 * q - (a + b + c) ** 2))

        h = (a + b) ** 2 + c ** 2
        vertex_test = 2*c*c - 2*b*c - a*c - a*b
        delta = a * (c - b) / (2 * c)
        w = [a - delta, b - delta, c]
        w_sq = (b*b + c*c) * (a*a + 2*a*c + 2*c*c) / (2*c*c)
        if vertex_test <= 0:
            vy, vertex_sq = [a, b, c], h
        else:
            vy, vertex_sq = w, w_sq

        f0 = f(h)
        bracket = None
        if f0 >= c:
            diameter_sq = h
            dx, dy = [Decimal(0)] * 3, [a, b, c]
            regime = "opposite_vertices"
        else:
            lo, hi = h, (a + c) ** 2 + b*b
            for _ in range(4 * precision):
                mid = (lo + hi) / 2
                if mid == lo or mid == hi:
                    break
                if f(mid) <= c:
                    lo = mid
                else:
                    hi = mid
            diameter_sq = (lo + hi) / 2
            x = (a - positive_sqrt(diameter_sq - (b + c) ** 2)) / 2
            y = (b - positive_sqrt(diameter_sq - (a + c) ** 2)) / 2
            dx, dy = [x, y, Decimal(0)], [a - x, b - y, c]
            bracket = {
                "squared_distance_lower": lo,
                "squared_distance_upper": hi,
                "F_lower_minus_c": f(lo) - c,
                "F_upper_minus_c": f(hi) - c,
            }
            regime = ("midline_radical" if a*a*b*b <= c*c*(b-a)*(a+b+2*c)
                      else "three_radical_root")

        data = {
            "input_sides": sides,
            "sorted_sides": [a,b,c],
            "sorted_axis_indices_zero_based": order,
            "opposite_vertex_distance": h.sqrt(),
            "fixed_vertex": {
                "X": [Decimal(0)] * 3,
                "Y": original(vy),
                "distance": vertex_sq.sqrt(),
                "distance_squared": vertex_sq,
                "test_H": vertex_test,
                "both_candidates_tie": vertex_test == 0,
                "second_tied_Y": original(w) if vertex_test == 0 else None,
            },
            "free_endpoints": {
                "X": original(dx),
                "Y": original(dy),
                "distance": diameter_sq.sqrt(),
                "distance_squared": diameter_sq,
                "regime": regime,
                "strictly_longer_than_fixed_vertex": f0 < c,
                "F_at_opposite_vertex_squared_minus_c": f0 - c,
                "five_unfolding_squared_lengths": antipodal_squared_distances(
                    a, b, c, dx[0], dx[1]),
                "numerical_root_bracket": bracket,
            },
            "decimal_precision": precision,
        }
        return data


def json_default(value):
    if isinstance(value, Decimal):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("a")
    parser.add_argument("b")
    parser.add_argument("c")
    parser.add_argument("--precision", type=int, default=70)
    args = parser.parse_args()
    if args.precision < 20:
        parser.error("precision must be at least 20 decimal digits")
    print(json.dumps(solve(args.a, args.b, args.c, args.precision),
                     default=json_default, indent=2))


if __name__ == "__main__":
    main()
