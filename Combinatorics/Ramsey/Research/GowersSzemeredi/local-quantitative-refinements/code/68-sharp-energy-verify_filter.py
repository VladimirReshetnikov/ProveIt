#!/usr/bin/env python3
"""Independent exact-integer audit of the degree-12 arity-16 filter.

All theorem checks use integers. Floating-point diagnostics are clearly
separated and have no role in acceptance. No assertions are used, so this
also runs correctly under python -O.
"""

import json
import math
from fractions import Fraction


def main():
    half = [1000, 942, 782, 558, 320, 124, 14]
    a = {j: half[abs(j)] for j in range(-6, 7)}
    s = sum(a.values())
    denominator = s * s
    b = {
        n: sum(a[j] * a.get(n - j, 0) for j in a)
        for n in range(-12, 13)
    }
    full = sum(value ** 16 for value in b.values())
    even = sum(value ** 16 for n, value in b.items() if n % 2 == 0)
    square = sum(value * value for value in b.values())

    checks = {
        "S_equals_6480": s == 6480,
        "denominator_equals_41990400": denominator == 41990400,
        "sum_coefficients_equals_one": sum(b.values()) == denominator,
        "coefficient_symmetry": all(b[n] == b[-n] for n in b),
        "all_coefficients_strictly_positive": all(value > 0 for value in b.values()),
        "strict_decrease_nonnegative_side": all(b[n] > b[n + 1] for n in range(12)),
        "P_strictly_exceeds_2_to_minus_49": full * 2 ** 49 > denominator ** 16,
        "gain_strictly_exceeds_481_over_250": 250 * full > 481 * even,
        "481_over_250_to_52_exceeds_2_to_49": 481 ** 52 > 2 ** 49 * 250 ** 52,
        "481_over_250_to_49_exceeds_2_to_46": 481 ** 49 > 2 ** 46 * 250 ** 49,
        "R2_strictly_below_2_to_minus_3": 8 * square < denominator ** 2,
        "cyclic_error_constant_equals_144": 24 + math.comb(16, 2) == 144,
        "common_threshold_constant_comparison": 576 * 2 ** 95 <= 4 ** 53,
        "common_retention_constant_comparison": 2 ** 103 <= 4 ** 53,
        "direct_cost_strictly_below_52": full ** 53 > denominator ** 16 * even ** 52,
        "optional_cost_strictly_below_103_over_2": full ** 105 > denominator ** 32 * even ** 103,
        "optional_threshold_exponent_z_strictly_below_48":
            full ** 49 > even ** 48 * square * denominator ** 14,
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise RuntimeError("Exact certificate failed: " + ", ".join(failed))

    p = Fraction(full, denominator ** 16)
    q = Fraction(even, denominator ** 16)
    gain = Fraction(full, even)
    r2 = Fraction(square, denominator ** 2)
    output = {
        "result": "All exact integer checks passed",
        "normalization": {"S": s, "coefficient_denominator": denominator},
        "coefficient_numerators_nonnegative_side": [b[n] for n in range(13)],
        "successive_positive_differences": [b[n] - b[n + 1] for n in range(12)],
        "P_numerator_before_reduction": full,
        "Q_numerator_before_reduction": even,
        "R2_numerator_before_reduction": square,
        "checks": checks,
        "noncertifying_float_diagnostics": {
            "P": float(p),
            "Q": float(q),
            "gain": float(gain),
            "R2": float(r2),
            "principal_cost": -math.log(float(p)) / math.log(float(gain)),
            "threshold_power": math.log(float(r2 / p)) / math.log(float(gain)),
        },
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
