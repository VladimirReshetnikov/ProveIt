#!/usr/bin/env python3
"""Run the article's exact order-32 to order-23 example."""
from fractions import Fraction
from spectral_core import (
    Root, increasing_core, realizable,
    fixed_point_realizable, fixed_point_free_realizable,
)


def main() -> None:
    p = {
        Root(1): 3,
        Root(Fraction(1, 2)): 2,
        Root(2): 4,
        Root(-2): 7,
        Root(0, 1): 5,
        Root(0, -1): 5,
        Root(0, 3): 3,
        Root(0, -3): 3,
    }
    core = increasing_core(p)
    print(f"Input degree: {sum(p.values())}")
    print(f"Core degree:  {sum(core.values())}")
    print("Retained roots (real part, imaginary part, multiplicity):")
    for root, multiplicity in sorted(core.items()):
        print(f"  ({root.re}, {root.im}, {multiplicity})")
    print(f"Core is exactly realizable: {realizable(core)}")
    print(f"Fixed-point realization exists: {fixed_point_realizable(core)}")
    print(f"Fixed-point-free realization exists: {fixed_point_free_realizable(core)}")


if __name__ == '__main__':
    main()
