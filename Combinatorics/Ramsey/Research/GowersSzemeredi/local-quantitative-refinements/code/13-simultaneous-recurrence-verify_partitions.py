#!/usr/bin/env python3
"""Deterministic finite checks for simultaneous linear phase partitions.

All phase, diameter, threshold, and rounding calculations use integers or
fractions.Fraction.  These checks accompany the proofs; they are not proofs
of the universal theorems.  Python 3.10+ and the standard library suffice.

Run:
    python3 verify_partitions.py

The default output is partition_verification.json beside this script.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from fractions import Fraction
from itertools import product
from pathlib import Path


def ceil_fraction(value: Fraction) -> int:
    return (value.numerator + value.denominator - 1) // value.denominator


def centered(value: int, modulus: int) -> int:
    residue = value % modulus
    return residue if 2 * residue <= modulus else residue - modulus


def arc_diameter(values: list[int], modulus: int) -> int:
    """Gowers's integer arc diameter, including sets of size one."""
    residues = sorted(set(value % modulus for value in values))
    assert residues
    gaps = [right - left for left, right in zip(residues, residues[1:])]
    gaps.append(residues[0] + modulus - residues[-1])
    return modulus - max(gaps)


def dirichlet_gap(modulus: int, slopes: list[int], grid: list[int]) -> int:
    """Rectangular pigeonhole, with no floating point computation."""
    budget = math.prod(grid)
    seen: dict[tuple[int, ...], int] = {}
    for index in range(budget + 1):
        box = tuple(
            side * ((index * slope) % modulus) // modulus
            for slope, side in zip(slopes, grid)
        )
        if box in seen:
            gap = index - seen[box]
            assert 1 <= gap <= budget
            for slope, side in zip(slopes, grid):
                assert abs(centered(gap * slope, modulus)) * side < modulus
            return gap
        seen[box] = index
    raise AssertionError("The rectangular pigeonhole collision was not found")


def chain_length(r: int, residue: int, gap: int) -> int:
    return (r - 1 - residue) // gap + 1


def flexible_budget(length: int, widths: list[Fraction]) -> tuple[list[int], int]:
    grid = [ceil_fraction(Fraction(2 * length - 2, 1) / eps) for eps in widths]
    return grid, length * math.prod(grid)


def prescribed_budget(target: int, widths: list[Fraction]) -> tuple[list[int], int]:
    grid = [ceil_fraction(Fraction(target - 1, 1) / eps) for eps in widths]
    return grid, (target - 1) * (target - 2) * math.prod(grid)


def partition_flexible(
    modulus: int, r: int, slopes: list[int], widths: list[Fraction], length: int
) -> tuple[int, list[tuple[int, int, int]]]:
    if length == 1:
        return 1, [(start, 1, 1) for start in range(r)]
    grid, budget = flexible_budget(length, widths)
    assert r >= budget
    gap = dirichlet_gap(modulus, slopes, grid)
    cells = []
    for residue in range(gap):
        size = chain_length(r, residue, gap)
        count, extra = divmod(size, length)
        assert count >= 1
        sizes = [length + extra] + [length] * (count - 1)
        cursor = residue
        for cell_size in sizes:
            cells.append((cursor, gap, cell_size))
            cursor += gap * cell_size
    return gap, cells


def partition_prescribed(
    modulus: int, r: int, slopes: list[int], widths: list[Fraction], target: int
) -> tuple[int, list[tuple[int, int, int]]]:
    if target <= 2:
        return 1, [(start, 1, 1) for start in range(r)]
    grid, budget = prescribed_budget(target, widths)
    assert r >= budget
    gap = dirichlet_gap(modulus, slopes, grid)
    cells = []
    lower = target - 1
    for residue in range(gap):
        size = chain_length(r, residue, gap)
        quotient, remainder = divmod(size, lower)
        assert quotient >= remainder
        sizes = [lower] * (quotient - remainder) + [target] * remainder
        assert sum(sizes) == size
        cursor = residue
        for cell_size in sizes:
            cells.append((cursor, gap, cell_size))
            cursor += gap * cell_size
    return gap, cells


def verify_partition(
    modulus: int,
    r: int,
    slopes: list[int],
    intercepts: list[int],
    widths: list[Fraction],
    target: int,
    prescribed: bool,
    gap: int,
    cells: list[tuple[int, int, int]],
) -> None:
    assert 1 <= r <= modulus
    assert len(slopes) == len(intercepts) == len(widths)
    assert cells and gap >= 1
    coverage = bytearray(r)
    for start, step, size in cells:
        assert step == gap and size >= 1
        if prescribed:
            assert size in (target - 1, target)
        else:
            assert target <= size <= 2 * target - 1
        points = [start + step * index for index in range(size)]
        assert len(set(points)) == size
        assert 0 <= points[0] <= points[-1] < r
        for point in points:
            assert coverage[point] == 0
            coverage[point] = 1
        for slope, intercept, eps in zip(slopes, intercepts, widths):
            diameter = arc_diameter(
                [slope * point + intercept for point in points], modulus
            )
            assert diameter * eps.denominator <= eps.numerator * modulus
    assert all(coverage)


def is_prime(number: int) -> bool:
    if number < 2:
        return False
    return all(number % divisor for divisor in range(2, math.isqrt(number) + 1))


def obstruction_witness(rng: random.Random) -> dict:
    modulus, r, length = 1009, 1000, 8
    widths = [Fraction(1, 4), Fraction(1, 4)]
    max_gap = (r - 1) // (length - 1)
    radius = [int(eps * modulus / (length - 1)) for eps in widths]
    union_numerator = max_gap * math.prod(2 * bound + 1 for bound in radius)
    union_denominator = modulus ** len(widths)
    assert is_prime(modulus) and modulus >= r
    assert union_numerator < union_denominator
    for attempt in range(1, 10001):
        slopes = [rng.randrange(modulus) for _ in widths]
        if all(
            any(
                abs(centered(gap * slope, modulus)) > bound
                for slope, bound in zip(slopes, radius)
            )
            for gap in range(1, max_gap + 1)
        ):
            # Arc diameter is invariant under translation, so the progression
            # starting at zero checks every possible start for this gap.
            for gap in range(1, max_gap + 1):
                diameters = [
                    arc_diameter(
                        [index * gap * slope for index in range(length)], modulus
                    )
                    for slope in slopes
                ]
                assert any(
                    diameter * eps.denominator > eps.numerator * modulus
                    for diameter, eps in zip(diameters, widths)
                )
            best_length, best_gap = 1, 1
            for gap in range(1, r):
                candidate_length = (r - 1) // gap + 1
                for slope, eps in zip(slopes, widths):
                    step = abs(centered(gap * slope, modulus))
                    if step:
                        candidate_length = min(
                            candidate_length, int(eps * modulus / step) + 1
                        )
                if candidate_length > best_length:
                    best_length, best_gap = candidate_length, gap
            attaining_diameters = [
                arc_diameter(
                    [index * best_gap * slope for index in range(best_length)],
                    modulus,
                )
                for slope in slopes
            ]
            assert all(
                diameter * eps.denominator <= eps.numerator * modulus
                for diameter, eps in zip(attaining_diameters, widths)
            )
            example_gap, example_cells = partition_prescribed(
                modulus, r, slopes, widths, 4
            )
            verify_partition(
                modulus, r, slopes, [0] * len(slopes), widths, 4, True,
                example_gap, example_cells,
            )
            return {
                "modulus": modulus,
                "interval_length": r,
                "forbidden_progression_length": length,
                "slopes": slopes,
                "widths": [str(eps) for eps in widths],
                "candidate_differences_checked": max_gap,
                "finite_union_bound_numerator": union_numerator,
                "finite_union_bound_denominator": union_denominator,
                "search_attempts": attempt,
                "all_candidate_differences_fail": True,
                "maximum_good_progression_length": best_length,
                "attaining_difference": best_gap,
                "attaining_centered_steps": [
                    centered(best_gap * slope, modulus) for slope in slopes
                ],
                "attaining_image_diameters": attaining_diameters,
                "prescribed_target_four_partition": {
                    "difference": example_gap,
                    "number_of_cells": len(example_cells),
                    "cell_lengths": sorted({cell[2] for cell in example_cells}),
                },
            }
    raise AssertionError("Failed to find the positive-probability witness")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20261006)
    parser.add_argument("--random-cases", type=int, default=300)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).with_name("partition_verification.json"),
    )
    args = parser.parse_args()
    rng = random.Random(args.seed)
    counts = {
        "total_partitions": 0,
        "flexible_partitions": 0,
        "prescribed_partitions": 0,
        "nontrivial_flexible_partitions": 0,
        "nontrivial_prescribed_partitions": 0,
        "target_one_cases": 0,
        "target_two_cases": 0,
        "exact_threshold_cases": 0,
        "composite_modulus_cases": 0,
        "checked_points": 0,
    }
    moduli = set()
    max_target = {"flexible": 0, "prescribed": 0}

    def run_case(modulus, r, slopes, intercepts, widths, target, prescribed):
        algorithm = partition_prescribed if prescribed else partition_flexible
        gap, cells = algorithm(modulus, r, slopes, widths, target)
        verify_partition(
            modulus, r, slopes, intercepts, widths, target, prescribed, gap, cells
        )
        mode = "prescribed" if prescribed else "flexible"
        counts["total_partitions"] += 1
        counts[mode + "_partitions"] += 1
        counts["checked_points"] += r
        counts["target_one_cases"] += target == 1
        counts["target_two_cases"] += target == 2
        counts["composite_modulus_cases"] += modulus > 1 and not is_prime(modulus)
        if (prescribed and target >= 3) or (not prescribed and target >= 2):
            counts["nontrivial_" + mode + "_partitions"] += 1
            budget_fn = prescribed_budget if prescribed else flexible_budget
            counts["exact_threshold_cases"] += r == budget_fn(target, widths)[1]
        max_target[mode] = max(max_target[mode], target)
        moduli.add(modulus)

    # Boundary target lengths, tiny moduli, and negative slopes/intercepts.
    for modulus in [1, 2, 3, 4, 6, 8, 9, 16, 17, 25, 32]:
        for r in sorted({1, modulus}):
            for target in [1, 2]:
                run_case(
                    modulus, r, [-3, 0, 7], [2, -5, 1],
                    [Fraction(1, 17), Fraction(1, 3), Fraction(2, 7)],
                    target, True,
                )
            run_case(
                modulus, r, [-3, 0, 7], [2, -5, 1],
                [Fraction(1, 17), Fraction(1, 3), Fraction(2, 7)], 1, False,
            )

    # Exhaust all 37^2 slope pairs for both exact finite threshold theorems.
    for slopes_tuple in product(range(37), repeat=2):
        slopes = list(slopes_tuple)
        widths = [Fraction(1, 2)] * 2
        run_case(37, 32, slopes, [5, 19], widths, 2, False)
        run_case(37, 32, slopes, [5, 19], widths, 3, True)

    # Test threshold equality and its immediate successors for a composite
    # modulus; residue differences need not be invertible for construction.
    for q in [1, 2, 3]:
        widths = [Fraction(1, 3)] * q
        for prescribed, target in [(False, 2), (False, 3), (True, 3), (True, 4)]:
            budget_fn = prescribed_budget if prescribed else flexible_budget
            threshold = budget_fn(target, widths)[1]
            modulus = 2 * (threshold + 3)
            for r in [threshold, threshold + 1, threshold + 2]:
                slopes = [rng.randrange(-modulus, modulus) for _ in range(q)]
                intercepts = [rng.randrange(modulus) for _ in range(q)]
                run_case(modulus, r, slopes, intercepts, widths, target, prescribed)

    modulus_pool = [
        1, 2, 3, 4, 6, 8, 9, 10, 12, 15, 17, 25, 31, 32, 37, 49, 64,
        97, 101, 128, 257, 512, 997, 1009, 2003, 4096, 10007, 65536,
    ]
    width_pool = [Fraction(1, 2), Fraction(1, 3), Fraction(2, 5),
                  Fraction(1, 4), Fraction(3, 7), Fraction(1, 8)]
    for _ in range(args.random_cases):
        modulus = rng.choice(modulus_pool)
        r = rng.randint(1, min(modulus, 20000))
        q = rng.randint(1, 4)
        slopes = [rng.randrange(-modulus, 2 * modulus) for _ in range(q)]
        intercepts = [rng.randrange(-modulus, 2 * modulus) for _ in range(q)]
        widths = [rng.choice(width_pool) for _ in range(q)]
        flexible_targets = [1] + [
            length for length in range(2, 26)
            if flexible_budget(length, widths)[1] <= r
        ]
        prescribed_targets = [1, 2] + [
            target for target in range(3, 26)
            if prescribed_budget(target, widths)[1] <= r
        ]
        run_case(
            modulus, r, slopes, intercepts, widths,
            rng.choice(flexible_targets), False,
        )
        run_case(
            modulus, r, slopes, intercepts, widths,
            rng.choice(prescribed_targets), True,
        )

    summary = {
        "status": "all checks passed",
        "purpose": "Reproducibility checks; not a substitute for the proofs",
        "arithmetic": "exact integers and fractions.Fraction; no floating point",
        "seed": args.seed,
        "random_case_pairs": args.random_cases,
        "exhaustive_family": "all 37^2 slope pairs at r=32, for both theorems",
        "counts": counts,
        "tested_moduli": sorted(moduli),
        "maximum_target_lengths": max_target,
        "checks": [
            "coverage and disjointness of the entire interval",
            "positive common difference and proper arithmetic progressions",
            "nonempty cells of the stated permitted lengths",
            "exact modular arc diameter for every phase on every cell",
            "rectangular pigeonhole step bounds",
            "integer threshold and conductor boundary cases",
            "prime and composite moduli, including modulus one",
        ],
        "finite_obstruction_witness": obstruction_witness(rng),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
