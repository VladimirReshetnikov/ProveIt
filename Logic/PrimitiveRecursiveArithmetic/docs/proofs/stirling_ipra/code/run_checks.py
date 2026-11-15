#!/usr/bin/env python3
"""Finite exact-rational validation for the iPRA Stirling package.

These tests are mathematical regression checks on explicitly bounded sets.
They do not constitute a proof for all inputs, a formal iPRA derivation, or
Lean verification. The accompanying manuscript proves the general claims.
Only Python's standard library is used. Floating point is not used.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import time

from stirling_rational import (
    bit_length, dyadic, e_approx, e_tail, exponent, factorial,
    log_approx, log_interval, log_series, log_series_tail,
    pi_approx, pi_interval, ratio_approx, ratio_interval, ratio_test,
    sqrt_lower, stirling_approx, stirling_interval, stirling_test,
    wallis_antiderivative, wallis_error_constant, wallis_integrand,
    wallis_product, wallis_sum,
)

COUNTS = Counter()


def check(condition, group, context=""):
    COUNTS[group] += 1
    if not condition:
        raise AssertionError(f"{group}: {context}")


def add(a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return out


def scale(c, a):
    return [c * x for x in a]


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def zero_polynomial(p):
    return all(x == 0 for x in p)


def intersection(a, b):
    return max(a[0], b[0]) <= min(a[1], b[1])


def leibniz_interval(terms):
    value = 4 * sum((F((-1) ** j, 2 * j + 1) for j in range(terms)), F(0))
    error = F(4, 2 * terms + 1)
    return (value, value + error) if terms % 2 == 0 else (value - error, value)


def rectangle_log_interval(q, mesh):
    """Independent left/right rectangle enclosures of integral_1^q dt/t."""
    if q < 1:
        low, high = rectangle_log_interval(1 / q, mesh)
        return -high, -low
    h = (q - 1) / mesh
    low = h * sum((1 / (1 + (j + 1) * h) for j in range(mesh)), F(0))
    high = h * sum((1 / (1 + j * h) for j in range(mesh)), F(0))
    return low, high


def check_basic_bounds():
    for n in range(501):
        b = bit_length(n)
        check(n < 2 ** b and (b == 0 or 2 ** (b - 1) <= n),
              "bounded_range_reduction", f"bit length n={n}")
    for a in range(1, 81):
        for b in range(1, a + 1):
            k = exponent(a, b)
            check(0 <= k <= a and 2 ** k * b <= a < 2 ** (k + 1) * b,
                  "bounded_range_reduction", f"a={a},b={b}")

    zs = [F(0), F(1, 20), F(1, 5), F(1, 3), F(1, 2), F(3, 4), F(-1, 3)]
    for z in zs:
        for terms in range(9):
            geometric = sum((z ** (2 * j) for j in range(terms)), F(0))
            check(1 / (1 - z * z) - geometric ==
                  z ** (2 * terms) / (1 - z * z),
                  "finite_atanh_enclosures", f"finite geometric z={z},K={terms}")
            for extra in (1, 2, 5, 12, 16):
                difference = sum(
                    (2 * z ** (2 * j + 1) / (2 * j + 1)
                     for j in range(terms, terms + extra)), F(0))
                check(abs(difference) <= log_series_tail(z, terms),
                      "finite_atanh_enclosures", f"z={z},K={terms},extra={extra}")

    for a in range(1, 21):
        for b in range(1, 8):
            q = F(a, b)
            for precision in range(6):
                low, high = log_interval(q, precision)
                check(low <= log_approx(q, precision) <= high and
                      high - low <= dyadic(precision),
                      "logarithm_error_bounds", f"q={q},p={precision}")
                check(intersection((low, high), log_interval(q, precision + 3)),
                      "logarithm_error_bounds", f"refined q={q},p={precision}")

    for q in (F(1, 4), F(1, 2), F(1), F(3, 2), F(2), F(3), F(10), F(31, 7)):
        for mesh in (8, 16, 32, 64):
            check(intersection(log_interval(q, 8), rectangle_log_interval(q, mesh)),
                  "independent_log_rectangles", f"q={q},N={mesh}")


def check_pi():
    for precision in range(31):
        low, high = pi_interval(precision)
        check(3 <= low <= pi_approx(precision) <= high <= 4,
              "pi_fast_enclosures", f"p={precision}")
        check(high - low <= dyadic(precision),
              "pi_fast_enclosures", f"tail p={precision}")
        check(intersection((low, high), pi_interval(precision + 3)),
              "pi_fast_enclosures", f"refinement p={precision}")

    for precision in range(9):
        for terms in (4, 8, 16, 32, 64, 128):
            check(intersection(pi_interval(precision), leibniz_interval(terms)),
                  "independent_pi_leibniz", f"p={precision},T={terms}")


def check_robbins():
    # Full coefficient checks, rather than a finite sample of polynomial values.
    # (12n+1)(12n+13) - 36(2n+1)^2 = 24n-23.
    lower_identity = add(
        add(mul([1, 12], [13, 12]), scale(-36, mul([1, 2], [1, 2]))),
        [23, -24])
    check(zero_polynomial(lower_identity), "polynomial_identities", "lower gap")
    # 4n(n+1) = (2n+1)^2-1.
    wallis_change = add(scale(4, mul([0, 1], [1, 1])),
                       add(scale(-1, mul([1, 2], [1, 2])), [1]))
    check(zero_polynomial(wallis_change), "polynomial_identities", "z substitution")
    # Clear 15(1-t) from t/[3(1-t)]-t/3-t^2/[5(1-t)]
    # -2t^2/[15(1-t)] = 0, where t=z^2.
    upper_identity = add(add([0, 5], scale(-5, mul([0, 1], [1, -1]))),
                         [0, 0, -5])
    check(zero_polynomial(upper_identity), "polynomial_identities", "upper gap")

    for n in range(1, 201):
        z = F(1, 2 * n + 1)
        lower_difference = F(1, 12 * n + 1) - F(1, 12 * n + 13)
        upper_difference = F(1, 12 * n) - F(1, 12 * (n + 1))
        ell = F(24 * n - 23,
                3 * (2 * n + 1) ** 2 * (12 * n + 1) * (12 * n + 13))
        eta = F(2, 15 * (2 * n + 1) ** 4)
        check(z * z / 3 - lower_difference == ell > 0,
              "local_robbins_gaps", f"lower n={n}")
        check(upper_difference -
              (z * z / 3 + z ** 4 / (5 * (1 - z * z))) ==
              2 * z ** 4 / (15 * (1 - z * z)) >= eta > 0,
              "local_robbins_gaps", f"upper n={n}")
        for terms in (1, 2, 4, 8):
            partial = sum((z ** (2 * j) / (2 * j + 1)
                           for j in range(1, terms + 1)), F(0))
            tail = z ** (2 * terms + 2) / ((2 * terms + 3) * (1 - z * z))
            check(lower_difference + ell <= partial,
                  "local_robbins_gaps", f"finite lower n={n},K={terms}")
            check(partial + tail <= upper_difference - eta,
                  "local_robbins_gaps", f"finite upper n={n},K={terms}")


def check_wallis():
    grid = 16
    for k in range(2, 11):
        for a in range(grid):
            for b in range(a + 1, grid + 1):
                u, v = F(a, grid), F(b, grid)
                h = v - u
                residual = (
                    wallis_antiderivative(k, v) - wallis_antiderivative(k, u)
                    - h * ((k - 1) * wallis_integrand(k - 2, u)
                           - k * wallis_integrand(k, u))
                )
                check(abs(residual) <= 8 * k * k * h * h,
                      "wallis_rational_increment", f"k={k},u={u},v={v}")

    meshes = (1, 2, 3, 5, 8, 16, 32, 64)
    for mesh in meshes:
        check(abs(wallis_sum(1, mesh) - 1) <= F(12, mesh),
              "wallis_sum_recurrence", f"base N={mesh}")
        for k in range(2, 21):
            residual = (k - 1) * wallis_sum(k - 2, mesh) - k * wallis_sum(k, mesh)
            check(abs(residual) <= F(8 * k * k, mesh),
                  "wallis_sum_recurrence", f"k={k},N={mesh}")
        i0 = wallis_sum(0, mesh)
        # Left rectangles for the decreasing w(t) have total width 1/N.
        p = pi_interval(12)
        check(intersection((i0 - F(1, mesh), i0), (p[0] / 2, p[1] / 2)),
              "independent_wallis_pi_rectangles", f"N={mesh}")

    for m in range(1, 11):
        p, q = F(1), F(1)
        for j in range(1, m + 1):
            p *= F(2 * j - 1, 2 * j)
            q *= F(2 * j, 2 * j + 1)
        w = wallis_product(m)
        check(p * q == F(1, 2 * m + 1) and q / p == w,
              "wallis_product_identities", f"m={m}")
        for mesh in meshes:
            i0 = wallis_sum(0, mesh)
            check(abs(wallis_sum(2 * m, mesh) - p * i0) <= F(8 * m * (m + 1), mesh),
                  "wallis_parity_bounds", f"even m={m},N={mesh}")
            check(abs(wallis_sum(2 * m + 1, mesh) - q) <=
                  F(8 * m * m + 16 * m + 12, mesh),
                  "wallis_parity_bounds", f"odd m={m},N={mesh}")
            error = F(wallis_error_constant(m), mesh)
            check(w - error <= i0 <= (1 + F(1, 2 * m)) * w + error,
                  "finite_wallis_D_bound", f"m={m},N={mesh}")


def check_main_predicates():
    for precision in range(13):
        check(stirling_approx(0, precision) == 0 and stirling_test(0, precision),
              "zero_input_conventions", f"Q(0,p),p={precision}")
        check(ratio_approx(0, precision) == 1 and ratio_test(0, precision),
              "zero_input_conventions", f"H(0,p),p={precision}")
    for n in range(1, 26):
        for precision in range(13):
            check(stirling_test(n, precision), "Q_predicate",
                  f"n={n},p={precision}")
            value = stirling_approx(n, precision)
            low, high = stirling_interval(n, precision)
            budget = dyadic(precision + 3)
            check(value - budget <= low <= high <= value + budget,
                  "Q_independent_error_budget", f"n={n},p={precision}")
            check(F(1, 12 * n + 1) < low <= high < F(1, 12 * n),
                  "independent_robbins_intervals", f"n={n},p={precision}")

    for n in range(1, 11):
        for precision in range(7):
            check(ratio_test(n, precision), "direct_ratio_predicate",
                  f"n={n},p={precision}")
            t = precision + 4 * n + 2
            q = 2 * n * pi_approx(t)
            root = sqrt_lower(q, t)
            check(root * root <= q < (root + dyadic(t)) ** 2,
                  "sqrt_square_certificates", f"n={n},p={precision}")
            check(0 < e_tail(t) <= dyadic(t),
                  "exp_factorial_tail", f"n={n},p={precision}")
            value = ratio_approx(n, precision)
            low, high = ratio_interval(n, precision)
            budget = 3 ** n * (3 * n + 1) * dyadic(t)
            check(budget <= dyadic(precision + 2),
                  "direct_ratio_error_budget", f"algebra n={n},p={precision}")
            check(value - budget <= low <= high <= value + budget,
                  "direct_ratio_error_budget", f"interval n={n},p={precision}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "validation" / "checks.json")
    args = parser.parse_args()
    started = time.monotonic()
    timings = {}
    for function in (check_basic_bounds, check_pi, check_robbins, check_wallis, check_main_predicates):
        before = time.monotonic()
        function()
        timings[function.__name__] = round(time.monotonic() - before, 4)
    source = Path(__file__).with_name("stirling_rational.py")
    result = {
        "status": "passed",
        "scope": "Finite exact-rational regression checks; not a formal proof of the universal theorem.",
        "arithmetic": "Python integers and fractions.Fraction; no floating point in mathematical checks",
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "reference_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "test_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "total_assertions": sum(COUNTS.values()),
        "assertions_by_group": dict(sorted(COUNTS.items())),
        "ranges": {
            "Q_predicate": "1 <= n <= 25; 0 <= p <= 12 (325 pairs)",
            "direct_ratio_predicate": "1 <= n <= 10; 0 <= p <= 6 (70 pairs)",
            "robbins_local": "1 <= n <= 200; truncation counts 1,2,4,8",
            "wallis_increments": "2 <= k <= 10; 0 <= u < v <= 1 on a denominator-16 grid",
            "wallis_sums": "N in 1,2,3,5,8,16,32,64; recurrence k=2..20; products m=1..10",
            "independent_pi": "fast precisions 0..8 against Leibniz term counts 4,8,16,32,64,128",
        },
        "timings_seconds": timings,
        "total_seconds": round(time.monotonic() - started, 4),
        "lean_compilation": "Not performed; no Lean executable was available.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "assertions": result["total_assertions"],
                      "seconds": result["total_seconds"], "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()

