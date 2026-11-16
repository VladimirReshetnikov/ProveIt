"""Reproducible finite regression checks; these are not proofs of generality.

Run from any directory with ``python3 path/to/code/verify.py``.  The output is
written beside this script as verification.json.  The mathematical paper, not
these tests, establishes completeness beyond the finite comparison windows.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path

from runge import (
    CertificateError, RungeCertificate, check_certificate,
    construct_certificate, coordinate_bounds, evaluate, hyperelliptic_family,
    isqrt_bounded, quartic_bounds, quartic_polynomial, solve_quartic_by_divisors,
    solve_with_certificate,
)


def independent_window(f: tuple[int, ...], window: int) -> list[tuple[int, int]]:
    """Use direct power evaluation and Python's separate math.isqrt routine."""
    result = set()
    for x in range(-window, window + 1):
        value = sum(a * x**i for i, a in enumerate(f))
        if value >= 0:
            y = isqrt(value)
            if y * y == value:
                result.add((x, y))
                result.add((x, -y))
    return sorted(result)


def rejects_constructor(f: tuple[int, ...]) -> bool:
    try:
        construct_certificate(f)
    except CertificateError:
        return True
    return False


def main() -> None:
    root_inputs = list(range(10001))
    for exponent in range(1, 129):
        root_inputs.extend([2**exponent - 1, 2**exponent, 2**exponent + 1])
    for n in root_inputs:
        assert isqrt_bounded(n) == isqrt(n)

    expected_family = [(-1, -1), (-1, 1), (0, -1), (0, 1)]
    family_results = []
    for m in range(2, 13):
        f = hyperelliptic_family(m)
        cert = construct_certificate(f)
        H, K = coordinate_bounds(f, cert)
        points = solve_with_certificate(f, cert)
        assert cert.D == 1 and cert.R == (1, 1)
        assert H == 2 and points == expected_family
        assert points == independent_window(f, 60)
        family_results.append({
            "m": m, "degree": 2 * m, "H": H, "K": K,
            "points": points, "comparison_window": [-60, 60],
        })

    quartic_cases = 0
    skipped_zero_delta = 0
    largest_comparison_window = 0
    forced_empty_cases = 0
    for a in range(-8, 9):
        for b in range(-8, 9):
            if a * a - 4 * b == 0:
                skipped_zero_delta += 1
                continue
            f = quartic_polynomial(a, b)
            cert = construct_certificate(f)
            H, K = coordinate_bounds(f, cert)
            points = solve_with_certificate(f, cert)
            divisors = solve_quartic_by_divisors(a, b)
            window = max(60, H + 3)
            brute = independent_window(f, window)
            assert points == divisors == brute
            tight = quartic_bounds(a, b)
            if tight["forced_empty"]:
                assert not points
                forced_empty_cases += 1
            for x, y in points:
                assert 4 * x * x <= tight["four_x_squared_bound"]
                assert 4 * abs(y) <= tight["four_abs_y_bound"]
                assert abs(x) <= H and abs(y) <= K
            quartic_cases += 1
            largest_comparison_window = max(largest_comparison_window, window)

    extra_results = []
    for f in [(1, 2, 3, 4, 1), (1, 0, 1, 0, 4)]:
        cert = construct_certificate(f)
        H, K = coordinate_bounds(f, cert)
        points = solve_with_certificate(f, cert)
        window = max(60, H + 3)
        assert points == independent_window(f, window)
        extra_results.append({
            "polynomial_ascending": f,
            "certificate": cert.to_dict(),
            "H": H, "K": K, "points": points,
            "comparison_window": [-window, window],
        })

    f = quartic_polynomial(7, 1)
    cert = construct_certificate(f)
    expected_quartic = [(-1, -3), (-1, 3), (0, -1), (0, 1), (1, -3), (1, 3)]
    assert solve_with_certificate(f, cert) == expected_quartic
    rejection_checks = {
        "zero_remainder": not check_certificate(
            (1, 0, 2, 0, 1), RungeCertificate(1, (1, 0, 1), ())),
        "wrong_identity": not check_certificate(
            f, RungeCertificate(cert.D, cert.A, (999,))),
        "zero_multiplier": not check_certificate(
            f, RungeCertificate(0, cert.A, cert.R)),
        "remainder_degree_too_large": not check_certificate(
            (0, 0, 1, 0, 1), RungeCertificate(1, (0, 0, 1), (0, 0, 1))),
        "constant_A": not check_certificate(
            (2,), RungeCertificate(1, (1,), (1,))),
        "constructor_square": rejects_constructor((1, 0, 2, 0, 1)),
        "constructor_odd_degree": rejects_constructor((1, 1, 0, 1)),
        "constructor_nonsquare_leading": rejects_constructor((1, 0, 0, 0, 2)),
        "constructor_negative_leading": rejects_constructor((1, 0, 0, 0, -1)),
    }
    assert all(rejection_checks.values())

    result = {
        "status": "all finite checks passed",
        "scope": (
            "Regression tests and independent finite comparisons only; "
            "the human-readable certificate proof establishes generality. "
            "No claim of a proof of general Siegel, an iPRA derivation, "
            "or Lean compilation is made by this JSON."
        ),
        "integer_square_root_checks": len(root_inputs),
        "hyperelliptic_family": family_results,
        "quartic_grid": {
            "a_range": [-8, 8], "b_range": [-8, 8],
            "nonzero_delta_cases": quartic_cases,
            "excluded_zero_delta_cases": skipped_zero_delta,
            "forced_empty_cases": forced_empty_cases,
            "largest_comparison_window": [-largest_comparison_window,
                                          largest_comparison_window],
            "comparisons": ["Runge certificate enumeration",
                            "signed divisor enumeration",
                            "independent brute-force x window"],
        },
        "featured_quartic": {
            "a": 7, "b": 1, "delta": 45,
            "certificate": cert.to_dict(),
            "sharp_bounds": quartic_bounds(7, 1),
            "complete_points": expected_quartic,
        },
        "extra_constructor_examples": extra_results,
        "rejection_checks": rejection_checks,
    }
    target = Path(__file__).with_name("verification.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "integer_square_root_checks": len(root_inputs),
        "family_cases": len(family_results),
        "quartic_cases": quartic_cases,
        "rejection_checks": len(rejection_checks),
        "output": str(target),
    }, indent=2))


if __name__ == "__main__":
    main()
