#!/usr/bin/env python3
"""Small exact checks of the compiler and interval-certificate implementation."""
from fractions import Fraction as Q
from pathlib import Path

from richardson import (Interval, PI, T, Evaluator, absolute, add, demo,
                        load_poly, magnitude_and_width, mul, pi_interval,
                        power, rat, sine_point, compile_reduction)


def main() -> None:
    checks = []

    def check(condition: bool, label: str) -> None:
        if not condition:
            raise AssertionError(label)
        checks.append(label)
        print("PASS:", label)

    a, b = Interval(Q(-2), Q(3)), Interval(Q(-5), Q(7))
    check((a * b) == Interval(Q(-15), Q(21)), "multiplication checks all four corners")
    check(a.abs() == Interval(Q(0), Q(3)), "absolute value across zero")
    check(a.negative_part_twice() == Interval(Q(0), Q(4)), "dependent negative-part image")
    check(sine_point(Q(0), 40) == Interval.point(0), "sine at zero is exact")
    pi = pi_interval(60)
    check(pi.lo > Q("3.141592653589793238") and pi.hi < Q("3.141592653589793240"),
          "Machin enclosure fits the expected rational bracket")
    check(Evaluator(Q(3, 2), 60).evaluate(power(T, 5)).contains(Q(243, 32)),
          "power compiler computes the fifth power")
    reused = Evaluator(Q(0), 10)
    check(all(reused.evaluate(rat(n)) == Interval.point(n) for n in range(100)),
          "reused evaluator retains ephemeral expression nodes without stale cache hits")
    base = Path(__file__).resolve().parent / "examples"
    root_poly = load_poly(base / "linear_root.json")
    reduction = compile_reduction(root_poly)
    check((root_poly.coefficient_bound, root_poly.degree_bound) == (2, 1),
          "coefficient and degree bounds for z-1")
    check(magnitude_and_width(reduction.identity, Q(1))[1] > 0,
          "a priori width recurrence is positive")
    results = demo(48)["certificates"]
    check(results[0]["certified_nonzero_at_this_input"],
          "z-1 reduction is certified nonzero at the supplied rational input")
    check(Q(results[0]["identity_interval"]["lo"]) > Q("1.999999999999"),
          "z-1 example has a rigorous value close to two")
    check(results[1]["identity_interval"]["lo"] == "0" and
          results[1]["identity_interval"]["hi"] == "0",
          "z+1 reduction vanishes at the sampled rational input")
    check(results[2]["identity_interval"]["lo"] == "0" and
          results[2]["identity_interval"]["hi"] == "0",
          "z^2+1 reduction vanishes at the sampled rational input")
    check(Q(results[3]["identity_interval"]["lo"]) == 2 and
          Q(results[3]["identity_interval"]["hi"]) == 2,
          "zero polynomial reduction equals two at t=0")
    print(f"\n{len(checks)} exact implementation checks passed.")
    print("These finite checks do not constitute the global mathematical proof.")


if __name__ == "__main__":
    main()
