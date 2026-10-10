#!/usr/bin/env python3
"""Exact Bernstein certificates for the universal Gaussian Euler bound.

Only Python's standard library is used.  Polynomial identities, interval
endpoints, and Bernstein coefficients are rational; no numerical optimizer
or floating-point sign test occurs in this verifier.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json


def clean(p):
    return {e: F(c) for e, c in p.items() if c}


def add(p, q, factor=1):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, F(0)) + factor * c
    return clean(r)


def scale(p, c):
    return clean({e: v * c for e, v in p.items()})


def mul(p, q):
    r = {}
    for e, c in p.items():
        for f, d in q.items():
            g = tuple(x + y for x, y in zip(e, f))
            r[g] = r.get(g, F(0)) + c * d
    return clean(r)


def power(p, n):
    r = {(0,) * len(next(iter(p))): F(1)}
    for _ in range(n):
        r = mul(r, p)
    return r


def divide_one_minus(p, axis):
    """Exact division by 1-x_axis, with a checked zero remainder."""
    dim = len(next(iter(p)))
    degree = max(e[axis] for e in p)
    others = sorted({tuple(e[i] for i in range(dim) if i != axis) for e in p})
    result = {}
    for f in others:
        cumulative = F(0)
        for j in range(degree + 1):
            e = f[:axis] + (j,) + f[axis:]
            cumulative += p.get(e, F(0))
            if j < degree and cumulative:
                result[e] = cumulative
        assert cumulative == 0
    return clean(result)


def on_unit_box(p, box):
    result = {}
    for e, c in p.items():
        for f in product(*(range(k + 1) for k in e)):
            value = c
            for k, j, (lo, hi) in zip(e, f, box):
                value *= comb(k, j) * lo ** (k - j) * (hi - lo) ** j
            result[f] = result.get(f, F(0)) + value
    return clean(result)


def bernstein_coefficients(p, box):
    dim = len(box)
    deg = tuple(max(e[i] for e in p) for i in range(dim))
    local = on_unit_box(p, box)
    values = []
    for r in product(*(range(k + 1) for k in deg)):
        value = F(0)
        for e, c in local.items():
            if all(i <= j for i, j in zip(e, r)):
                for i, j, k in zip(e, r, deg):
                    c *= F(comb(j, i), comb(k, i))
                value += c
        values.append(value)
    return values


def certify_positive(p, name):
    dim = len(next(iter(p)))
    pending = [(((F(0), F(1)),) * dim, 0)]
    cells = []
    while pending:
        box, depth = pending.pop()
        coefficients = bernstein_coefficients(p, box)
        low = min(coefficients)
        if low > 0:
            cells.append({
                "box": [[str(lo), str(hi)] for lo, hi in box],
                "minimum_bernstein_coefficient": str(low),
                "coefficient_count": len(coefficients),
            })
            continue
        assert depth < 10, (name, box, low)
        halves = []
        for lo, hi in box:
            mid = (lo + hi) / 2
            halves.append(((lo, mid), (mid, hi)))
        pending.extend((tuple(child), depth + 1) for child in product(*halves))
    cells.sort(key=lambda cell: cell["box"])
    total_volume = sum(
        (product_volume(cell["box"]) for cell in cells), F(0)
    )
    assert total_volume == 1
    return {
        "name": name,
        "polynomial": [
            {"exponents": list(e), "coefficient": str(c)}
            for e, c in sorted(p.items())
        ],
        "cell_count": len(cells),
        "coefficient_count": sum(c["coefficient_count"] for c in cells),
        "minimum_coefficient": str(min(F(c["minimum_bernstein_coefficient"]) for c in cells)),
        "cells": cells,
    }


def product_volume(box):
    volume = F(1)
    for lo, hi in box:
        volume *= F(hi) - F(lo)
    return volume


def polynomial_n(n):
    one = {(0, 0): F(1)}
    x = {(1, 0): F(1)}
    xy2 = {(1, 2): F(1)}
    numerator = add(
        mul(power(add(one, xy2, -1), n), add(one, x)),
        mul(power(add(one, x, -1), n), add(one, xy2)), -1,
    )
    divided = divide_one_minus(numerator, 1)
    # P_n / [8(1+x)(1+xy^2)] = 9/8 - K_n(sqrt(x), y).
    denominator = mul(add(one, x), add(one, xy2))
    return add(scale(denominator, 9), scale(divided, -8))


def polynomial_fourth_power():
    one = {(0,): F(1)}
    t3, t8 = {(3,): F(1)}, {(8,): F(1)}
    p = add(
        scale(power(add(one, t8, -1), 3), 9),
        scale(mul(power(add(one, t3, -1), 3), power(add(one, t3), 4)), -8),
    )
    for _ in range(3):
        p = divide_one_minus(p, 0)
    return p


def main():
    results = [certify_positive(polynomial_n(n), f"P_{n}") for n in (2, 3)]
    results.append(certify_positive(polynomial_fourth_power(), "Q_4"))
    # A finite exact witness that the first-step axis value exceeds 9/8.
    # At a=0,b=1, -2E_8 < C(1), because all later increments are negative.
    harmonic = F(0)
    finite_sum = F(0)
    for k in range(8):
        if k:
            harmonic += F(1, 2*k-1) + F(1, 2*k)
        finite_sum += (-1)**k * harmonic * sum(comb(8, j) for j in range(k+1, 9))
    axis_lower = -2 * finite_sum / 2**8
    assert axis_lower == F(1627631, 1441440)
    assert axis_lower > F(9, 8)
    output = {
        "arithmetic": "exact fractions; no floating-point sign decisions",
        "bound": "9/8",
        "status": "PASS",
        "axis_C1_strict_lower_bound": str(axis_lower),
        "results": results,
    }
    destination = Path(__file__).resolve().parents[1] / "data" / "euler_polynomial_certificate.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(output, indent=2) + "\n")
    for row in results:
        print(f"{row['name']}: PASS; {row['cell_count']} boxes; "
              f"{row['coefficient_count']} positive coefficients; "
              f"minimum = {row['minimum_coefficient']}")


if __name__ == "__main__":
    main()
