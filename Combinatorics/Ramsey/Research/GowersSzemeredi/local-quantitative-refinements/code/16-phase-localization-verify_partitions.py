#!/usr/bin/env python3
"""Exact verification of the own-step progression partition construction.

Uses only Python's standard library.  Every comparison is rational/integer;
the output reports successful finite certificates, not a numerical test of
the external uniform recurrence theorem.  Run with --output PATH to save JSON.
"""

from argparse import ArgumentParser
from fractions import Fraction
import json
from math import ceil, prod
from pathlib import Path


def norm_numerator(value, modulus):
    residue = value % modulus
    return min(residue, modulus - residue)


def split_lengths(length, minimum):
    quotient, remainder = divmod(length, minimum)
    assert quotient >= 1
    return [minimum] * (quotient - 1) + [minimum + remainder]


def verify_case(modulus, interval_length, slopes, intercepts, minimum, tolerances):
    subdivisions = [ceil(2 / tolerance) for tolerance in tolerances]
    step_budget = prod(subdivisions)
    block_minimum = minimum * step_budget
    recurrence_tolerances = [
        tolerance / (4 * minimum * step_budget**2)
        for tolerance in tolerances
    ]
    certificate = next(
        (
            candidate
            for candidate in range(1, interval_length // block_minimum + 1)
            if all(
                Fraction(norm_numerator(slope * candidate**2, modulus), modulus)
                <= tolerance
                for slope, tolerance in zip(slopes, recurrence_tolerances)
            )
        ),
        None,
    )
    result = {
        "modulus": modulus,
        "interval_length": interval_length,
        "slopes_numerators": slopes,
        "intercepts_numerators": intercepts,
        "minimum_length": minimum,
        "tolerances": list(map(str, tolerances)),
        "step_budget": step_budget,
        "recurrence_certificate": certificate,
    }
    if certificate is None:
        result["status"] = "no_certificate_at_this_finite_size"
        return result

    coverage = [0] * interval_length
    cell_count = 0
    least_length = interval_length
    greatest_length = 0
    common_differences = set()
    greatest_errors = [Fraction(0) for _ in slopes]
    for residue in range(certificate):
        fibre = list(range(residue, interval_length, certificate))
        start = 0
        for length in split_lengths(len(fibre), block_minimum):
            block = fibre[start : start + length]
            start += length
            base = block[0]
            linear_step = next(
                candidate
                for candidate in range(1, step_budget + 1)
                if all(
                    Fraction(
                        norm_numerator(
                            (slope * base + intercept) * certificate * candidate,
                            modulus,
                        ),
                        modulus,
                    )
                    <= tolerance / 2
                    for slope, intercept, tolerance
                    in zip(slopes, intercepts, tolerances)
                )
            )
            for second_residue in range(linear_step):
                second_fibre = block[second_residue::linear_step]
                second_start = 0
                for count in split_lengths(len(second_fibre), minimum):
                    cell = second_fibre[second_start : second_start + count]
                    second_start += count
                    common_difference = certificate * linear_step
                    assert all(
                        cell[index + 1] - cell[index] == common_difference
                        for index in range(len(cell) - 1)
                    )
                    cell_count += 1
                    least_length = min(least_length, len(cell))
                    greatest_length = max(greatest_length, len(cell))
                    common_differences.add(common_difference)
                    for point in cell:
                        coverage[point] += 1
                        for index, (slope, intercept, tolerance) in enumerate(
                            zip(slopes, intercepts, tolerances)
                        ):
                            actual = Fraction(
                                norm_numerator(
                                    (slope * point + intercept) * common_difference,
                                    modulus,
                                ),
                                modulus,
                            )
                            assert actual <= tolerance
                            greatest_errors[index] = max(greatest_errors[index], actual)

    assert all(multiplicity == 1 for multiplicity in coverage)
    assert minimum <= least_length <= greatest_length <= 2 * minimum - 1
    result.update(
        status="verified",
        recurrence_errors=[
            str(Fraction(norm_numerator(slope * certificate**2, modulus), modulus))
            for slope in slopes
        ],
        recurrence_tolerances=list(map(str, recurrence_tolerances)),
        cell_count=cell_count,
        cell_length_range=[least_length, greatest_length],
        common_differences=sorted(common_differences),
        greatest_own_step_errors=list(map(str, greatest_errors)),
        exact_coverage=True,
    )
    return result


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    cases = [
        (65537, 65537, [1020], [23456], 3, [Fraction(1, 4)]),
        (
            120000,
            40000,
            [32000, 16000],
            [12345, 67890],
            4,
            [Fraction(1, 3), Fraction(1, 4)],
        ),
        # This finite example intentionally has no recurrence certificate.
        (100003, 100003, [1020, 2040], [23456, 45678], 3, [Fraction(1, 2)] * 2),
    ]
    results = {
        "arithmetic": "exact integer residues and fractions.Fraction",
        "cases": [verify_case(*case) for case in cases],
    }
    assert results["cases"][0]["status"] == "verified"
    assert results["cases"][1]["status"] == "verified"
    assert results["cases"][2]["status"] == "no_certificate_at_this_finite_size"
    serialized = json.dumps(results, indent=2) + "\n"
    if arguments.output:
        arguments.output.write_text(serialized, encoding="utf-8")
    print(serialized, end="")


if __name__ == "__main__":
    main()
