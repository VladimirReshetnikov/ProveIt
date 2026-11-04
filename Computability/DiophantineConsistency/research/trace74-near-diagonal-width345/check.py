#!/usr/bin/env python3
"""Check finite constants and affine exponent bookkeeping in the note.

This is not a universal verification of the mathematical inequalities or a
Lean proof. Run without Python optimization so assertions remain enabled.
"""
import sys

if sys.flags.optimize:
    raise SystemExit("optimized Python disables required assertions")

for c, expected_margin in ((3, 76), (4, 61), (5, 26)):
    # d = n - 4c, r <= n+c <= d+5c.
    threshold = 4 * c
    assert threshold >= 3 * c
    # Raising K <= 2^(5c) P to 2c introduces 10c^2.
    coefficient_bits = 5 * c - 1 + 10 * c * c
    margin = 60 * c - coefficient_bits
    assert margin == expected_margin and margin > 0
    # q^3 >= 2^(2c) follows from q >= 2^30.
    assert 90 >= 2 * c
    print(f"c={c}: n>={threshold}, q-power margin={margin} bits")

print("PASS: finite exponent comparisons only")
