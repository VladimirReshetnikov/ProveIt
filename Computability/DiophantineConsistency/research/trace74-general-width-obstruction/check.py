#!/usr/bin/env python3
"""Check illustrative affine-threshold computations, not the proof."""
import sys

if sys.flags.optimize:
    raise SystemExit("optimized Python disables required assertions")


def minimum_n(base_bits: int, width: int) -> int:
    slope = 3 * base_bits - 2 * width
    assert slope > 0
    intercept = (10 * base_bits + 5) * width + 2 * width * width - 1
    return max(3 * width, intercept // slope + 1)


for width, expected in ((3, 12), (4, 16), (5, 20), (6, 25), (44, 8646)):
    actual = minimum_n(30, width)
    assert actual == expected
    margin = (90 - 2 * width) * actual - (305 * width + 2 * width**2 - 1)
    assert margin > 0
    print(f"B=30 c={width}: n>={actual}, threshold margin={margin}")

base_bits = 67 * 8807
assert base_bits == 590069
maximum_width = (3 * base_bits - 1) // 2
assert maximum_width == 885103
assert 2 * maximum_width < 3 * base_bits <= 2 * (maximum_width + 1)
print(f"B={base_bits}: largest allowed fixed c={maximum_width}")
print("PASS: finite threshold calculations only")
