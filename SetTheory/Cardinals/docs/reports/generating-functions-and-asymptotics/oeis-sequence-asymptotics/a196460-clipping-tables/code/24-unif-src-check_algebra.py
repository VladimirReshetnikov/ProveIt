#!/usr/bin/env python3
"""Fresh exact polynomial and discrete-Gaussian algebra checks."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def add(a, b):
    out = [F(0)]*max(len(a), len(b))
    for i, value in enumerate(a):
        out[i] += value
    for i, value in enumerate(b):
        out[i] += value
    return out


def mul(a, b):
    out = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def scale(a, scalar):
    return [scalar*x for x in a]


def shift(a, t):
    return [sum(F(a[j])*comb(j, i)*t**(j-i) for j in range(i, len(a)))
            for i in range(len(a))]


def main():
    high = add(scale(mul(mul([-2, 1], [-1, 2]), [1, 1, 3]), 12),
               scale(mul(mul([0, 1], [1, 1]), [2, -15, 13]), -5))
    assert high == [24, -46, 101, -146, 7]
    four = add(scale([-2, 41, -66, 27], 27),
               scale([3, 5, -6, 13], -52))
    assert four == [-210, 847, -1470, 53]
    merged = add(mul([-1, -18, 4], [-1, 3]), scale([2, -15, 13], -1))
    assert merged == [-1, 30, -71, 12]
    assert all(x > 0 for x in shift(high, 21))
    assert all(x > 0 for x in shift(four, 28))
    assert all(x > 0 for x in shift(merged, 6))
    assert F(13, 2)+2*(F(16, 9)-F(27, 16)) == F(481, 72) < 8
    assert 50 < 64  # (5 sqrt(2))^2 < 8^2
    assert 1+2*(F(20, 27)-F(1, 4)) == F(107, 54) < 2
    assert F(20, 27)+F(4, 9)+F(1, 3) == F(41, 27) < 2
    assert F(68, 55)**2 < 2
    assert F(33, 32)**4 < 2
    moments = []
    for k in range(129):
        weights = [comb(k, r)*(1 << (r*(k-r))) for r in range(k+1)]
        moment = sum(F((2*r-k)**2, 4)*w for r, w in enumerate(weights))/sum(weights)
        assert 0 <= moment < 2
        if k in (0, 1, 2, 8, 16, 32, 64, 128):
            moments.append({"k": k, "second_moment": str(moment)})
    result = {"status": "PASS", "polynomial_comparisons": 3,
              "positive_shift_certificates": {
                  "high_at_21": [str(x) for x in shift(high, 21)],
                  "four_at_28": [str(x) for x in shift(four, 28)],
                  "merged_at_6": [str(x) for x in shift(merged, 6)]},
              "alpha_weight_second_moment_checks": 129,
              "selected_second_moments": moments}
    with (HERE / "evidence/algebra.json").open("x") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print("PASS: three polynomial differences, positive shift certificates,")
    print("Gaussian geometric sums, ratio constants, and 129 second moments.")


if __name__ == "__main__":
    main()
