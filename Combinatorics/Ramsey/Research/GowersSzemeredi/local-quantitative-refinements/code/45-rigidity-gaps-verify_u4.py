#!/usr/bin/env python3
"""Exact certificates for the real U4 norm gap. Standard library only.

From the extracted package root:
    python3 code/verify_u4.py --json certificates/u4_certificate.json

All mathematical checks use integer or rational arithmetic.  The JSON report
is deterministic and contains the intermediate finite counting certificates.
"""

if not __debug__:
    raise SystemExit("Do not use Python -O or -OO: this verifier requires assertions.")

import argparse
import json
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, prod
from pathlib import Path

REPORT = {"status": "pending", "arithmetic": "exact integers and fractions"}


def add(p, q):
    out = [F(0)] * max(len(p), len(q))
    for i, c in enumerate(p):
        out[i] += c
    for i, c in enumerate(q):
        out[i] += c
    return out


def scale(c, p):
    return [c * x for x in p]


def multiply(p, q):
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def cube_histogram(values, dimension):
    n = len(values)
    vertices = list(product((0, 1), repeat=dimension))
    hist = Counter()
    for x_and_h in product(range(n), repeat=dimension + 1):
        x, *h = x_and_h
        cube_value = prod(
            values[(x + sum(e * step for e, step in zip(v, h))) % n]
            for v in vertices
        )
        hist[cube_value] += 1
    assert sum(hist.values()) == n ** (dimension + 1)
    return hist


def check_rational_certificate():
    a, b = F(99, 676), F(33, 26)
    p = [-a, b, -F(1, 4)]
    # 10 t^2 - 4P(t) = 11(t - 3/13)^2.
    left = add([0, 0, 10], scale(-4, p))
    right = scale(11, multiply([-F(3, 13), 1], [-F(3, 13), 1]))
    assert left == right
    p_squared = multiply(p, p)
    assert add([0, 0, 0, 0, 1], scale(-2, p_squared)) == [
        -2 * a * a,
        4 * a * b,
        -F(2277, 676),
        F(33, 26),
        F(7, 8),
    ]
    # Substitute W=V-1, A=35/8, B=5/2 in the Jensen bound.
    lower = add(
        [
            F(7, 8) * F(35, 8) + F(33, 26) * F(5, 2)
            + 4 * a * b - 2 * a * a,
            -F(2277, 676),
        ],
        scale(2, multiply([F(83, 676), F(3, 4)], [F(83, 676), F(3, 4)])),
    )
    target = add(
        [F(4795, 832)],
        add(scale(F(3, 8), [-F(3, 2), 1]),
            scale(F(9, 8), multiply([-F(3, 2), 1], [-F(3, 2), 1]))),
    )
    assert lower == target
    REPORT["quadratic_certificate"] = {
        "a": str(a), "b": str(b), "constant": "4795/832",
        "pointwise_identity": "10*t^2 - 4*P(t) = 11*(t-3/13)^2",
        "final_polynomial": "4795/832 + (3/8)*(V-3/2) + (9/8)*(V-3/2)^2",
        "lower_polynomial_coefficients": [str(c) for c in lower],
    }
    print("Rational U4 certificate: 4795/832, all polynomial identities exact.")


def check_cosine_sign_counts():
    vertices = list(product((0, 1), repeat=4))
    nonzero = vertices[1:]
    dual = Counter()
    for signs in product((-1, 1), repeat=15):
        if all(sum(s * v[i] for s, v in zip(signs, nonzero)) == 0
               for i in range(4)):
            dual[sum(signs)] += 1
    assert dual == {-5: 1, -3: 27, -1: 111, 1: 111, 3: 27, 5: 1}

    # Independent integer dynamic programming on the generating product.
    dp = {(0, 0, 0, 0, 0): 1}
    for v in nonzero:
        new = defaultdict(int, dp)
        for key, multiplicity in dp.items():
            size, *coordinates = key
            next_coordinates = tuple(c + e for c, e in zip(coordinates, v))
            if max(next_coordinates) <= 4:
                new[(size + 1,) + next_coordinates] += multiplicity
        dp = dict(new)
    subset_counts = {
        size: multiplicity
        for (size, *coordinates), multiplicity in dp.items()
        if coordinates == [4, 4, 4, 4]
    }
    assert subset_counts == {5: 1, 6: 27, 7: 111, 8: 111, 9: 27, 10: 1}
    assert {2 * size - 15: c for size, c in subset_counts.items()} == dual
    REPORT["cosine_dual_counts"] = dict(sorted(dual.items()))
    REPORT["cosine_subset_counts"] = dict(sorted(subset_counts.items()))
    REPORT["cosine_full_cube_counts"] = {}

    for q in (3, 5, 7, 9):
        counts = Counter()
        for signs in product((-1, 1), repeat=16):
            total = sum(signs)
            if total % q == 0 and all(
                sum(s * v[i] for s, v in zip(signs, vertices)) % q == 0
                for i in range(4)
            ):
                counts[total] += 1
        expected = ({-12: 8, -6: 16, 0: 286, 6: 16, 12: 8}
                    if q == 3 else {0: 222})
        assert counts == expected
        REPORT["cosine_full_cube_counts"][q] = dict(sorted(counts.items()))
    print("Cosine dual counts verified by enumeration and independent generating DP.")
    print("Order-three phase polynomial: 286 + 32 cos(6 theta) + 16 cos(12 theta).")


def check_five_point_example():
    f = [2, 1, -2, -2, 1]
    assert sum(f) == 0
    expected_q = {2: F(94, 25), 3: F(19208, 625), 4: F(6468874, 3125)}
    expected_h4 = {
        -2048: 160, -1024: 320, -512: 160, -64: 32,
        1: 10, 16: 80, 256: 760, 512: 320, 1024: 800,
        2048: 32, 4096: 320, 16384: 80, 65536: 51,
    }
    REPORT["five_point_example"] = {"modulus": 5, "values": f, "cubes": {}}
    for d in (2, 3, 4):
        histogram = cube_histogram(f, d)
        q = F(sum(value * count for value, count in histogram.items()), 5 ** (d + 1))
        assert q == expected_q[d]
        REPORT["five_point_example"]["cubes"][d] = {
            "average": str(q),
            "number_of_cubes": 5 ** (d + 1),
            "product_sum": sum(value * count for value, count in histogram.items()),
            "histogram": dict(sorted(histogram.items())),
        }
        print(f"Q_{d} = {q}; histogram = {dict(sorted(histogram.items()))}")
        if d == 4:
            assert histogram == expected_h4
    ratio_fourth = expected_q[2] ** 4 / expected_q[4]
    assert ratio_fourth == F(39037448, 404304625)
    assert ratio_fourth > F(8, 111)
    assert expected_q[4] >= F(4795, 832) * expected_q[2] ** 4
    REPORT["five_point_example"]["quotient_fourth_power"] = str(ratio_fourth)
    print(f"Exact c4 lower endpoint to the fourth power: {ratio_fourth}")


def check_pairing_coefficients():
    # Finite sanity check of the universal coefficientwise factorial inequality.
    # The general proof is the multinomial theorem in the notes.
    for m in range(1, 9):
        for k in product(range(m + 1), repeat=4):
            if sum(k) == m:
                assert prod(factorial(ki) for ki in k) <= factorial(m)
    assert [F(comb(2 * m, m), 2 ** m) for m in range(1, 5)] == [
        F(1), F(3, 2), F(5, 2), F(35, 8)
    ]
    REPORT["even_moment_coefficients"] = [
        str(F(comb(2 * m, m), 2 ** m)) for m in range(1, 5)
    ]
    print("Even-moment coefficient constants: 1, 3/2, 5/2, 35/8.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write the exact certificate report as JSON")
    args = parser.parse_args()
    check_rational_certificate()
    check_cosine_sign_counts()
    check_five_point_example()
    check_pairing_coefficients()
    REPORT["status"] = "all exact certificate checks passed"
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(REPORT, indent=2, sort_keys=True) + "\n",
                             encoding="utf-8")
        print(f"Wrote exact JSON certificate: {args.json}")
    print("All exact certificate checks passed.")
