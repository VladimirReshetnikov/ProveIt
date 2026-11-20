#!/usr/bin/env python3
"""Exact-rational calculations accompanying the measure and integration section.

This program evaluates and checks finite formulas.  It is not a proof checker
for iPRA and does not assert convergence merely from the checked examples.
Use: python3 measure_reference.py --output ../evidence/measure_checks.json
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path


def integral(weights: tuple[Q, ...], values: tuple[Q, ...]) -> Q:
    if len(weights) != len(values):
        raise ValueError("mismatched finite table lengths")
    if any(w < 0 for w in weights):
        raise ValueError("measure weights must be nonnegative")
    return sum((w * a for w, a in zip(weights, values)), Q(0))


def clip(value: Q, height: Q) -> Q:
    if height < 0:
        raise ValueError("negative clipping height")
    return min(height, max(-height, value))


def tail(weights: tuple[Q, ...], values: tuple[Q, ...], height: Q) -> Q:
    return integral(weights, tuple(max(abs(a) - height, Q(0)) for a in values))


def vitali_bound(weights: tuple[Q, ...], u: tuple[Q, ...], v: tuple[Q, ...],
                 height: Q, delta: Q) -> dict[str, Q]:
    if delta <= 0 or height < 0:
        raise ValueError("positive delta and nonnegative height required")
    difference = tuple(abs(a - b) for a, b in zip(u, v))
    if len(difference) != len(weights) or len(u) != len(v):
        raise ValueError("mismatched finite table lengths")
    bad = tuple(Q(int(d > delta)) for d in difference)
    lhs = integral(weights, difference)
    mass = sum(weights, Q(0))
    eta = integral(weights, bad)
    clipping = tuple(abs(clip(a, height) - clip(b, height)) for a, b in zip(u, v))
    clipped_integral = integral(weights, clipping)
    tail_u, tail_v = tail(weights, u, height), tail(weights, v, height)
    rhs = tail_u + tail_v + delta * mass + 2 * height * eta
    assert clipped_integral <= delta * mass + 2 * height * eta
    assert lhs <= rhs
    return {"lhs": lhs, "rhs": rhs, "tail_u": tail_u, "tail_v": tail_v,
            "bad_mass": eta, "total_mass": mass, "clipped_l1": clipped_integral}


def fubini(wx: tuple[Q, ...], wy: tuple[Q, ...], rows: tuple[tuple[Q, ...], ...]) -> dict[str, Q]:
    if len(rows) != len(wx) or any(len(row) != len(wy) for row in rows):
        raise ValueError("mismatched rectangular table")
    jy = tuple(integral(wy, row) for row in rows)
    jx = tuple(integral(wx, tuple(row[j] for row in rows)) for j in range(len(wy)))
    xy = integral(wx, jy)
    yx = integral(wy, jx)
    norm = integral(wx, tuple(integral(wy, tuple(abs(a) for a in row)) for row in rows))
    jy_norm = integral(wx, tuple(abs(a) for a in jy))
    jx_norm = integral(wy, tuple(abs(a) for a in jx))
    assert xy == yx
    assert jy_norm <= norm and jx_norm <= norm
    return {"xy_integral": xy, "yx_integral": yx, "product_l1": norm,
            "partial_y_l1": jy_norm, "partial_x_l1": jx_norm}


def check_finite_vitali() -> int:
    values = tuple(map(Q, (-2, -1, 0, 1, 2)))
    weights = (Q(0), Q(1, 3), Q(2, 3))
    count = 0
    for w, a, b, height, delta in itertools.product(
            itertools.product(weights, repeat=2),
            itertools.product(values, repeat=2),
            itertools.product(values, repeat=2), (Q(0), Q(1), Q(2)), (Q(1, 4), Q(1))):
        vitali_bound(w, a, b, height, delta)
        count += 1
    return count


def check_fubini() -> int:
    count = 0
    # Total masses need not be one; contraction is still exactly constant one.
    for a in itertools.product((Q(-2), Q(0), Q(3)), repeat=4):
        fubini((Q(1, 3), Q(4, 3)), (Q(1, 2), Q(3, 4)), (a[:2], a[2:]))
        count += 1
    return count


def moving_spike_examples() -> list[dict[str, Q | int]]:
    result = []
    for n in range(10):
        event_mass = Q(3, 4 ** (n + 1))
        height = Q(2 ** n)
        norm = height * event_mass
        assert norm == Q(3, 4 * 2 ** n)
        integral_partial = sum((Q(3, 4 * 2 ** j) for j in range(n)), Q(0))
        remaining = Q(3, 2 * 2 ** n)
        square_partial = sum((Q(4 ** j) * Q(3, 4 ** (j + 1)) for j in range(n)), Q(0))
        assert integral_partial + remaining == Q(3, 2)
        assert square_partial == Q(3 * n, 4)
        result.append({"n": n, "height": height, "support_mass": event_mass,
                       "spike_l1": norm, "majorant_partial_integral": integral_partial,
                       "majorant_tail": remaining, "majorant_square_partial_integral": square_partial})
    return result


def encode(value):
    if isinstance(value, Q):
        return str(value)
    raise TypeError(f"cannot encode {type(value)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = {
        "scope": "exact finite arithmetic examples, not formal iPRA derivations",
        "finite_vitali_cases": check_finite_vitali(),
        "finite_fubini_cases": check_fubini(),
        "example_vitali": vitali_bound((Q(1, 8), Q(3, 8), Q(1, 2)),
                                       (Q(8), Q(-2), Q(1, 4)), (Q(0), Q(0), Q(0)), Q(1), Q(1, 2)),
        "example_fubini": fubini((Q(1, 3), Q(2, 3)), (Q(1, 4), Q(3, 4)),
                                  ((Q(2), Q(-1)), (Q(3), Q(4)))),
        "moving_spikes": moving_spike_examples(),
        "result": "all finite checks passed",
    }
    text = json.dumps(data, indent=2, default=encode) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
