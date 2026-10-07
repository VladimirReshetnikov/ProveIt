#!/usr/bin/env python3
"""Exact finite diagnostics for the torsion-free energy theorems.

The checker uses Python's standard library only. Pair-difference energy,
ordered missing completions, and positive Schur counts are computed by
different loops. Exhaustion covers the finite boxes recorded in the JSON;
the mathematical proofs, rather than these checks, cover arbitrary sets.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import platform


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def maximum_energy(size: int) -> int:
    return (2 * size**3 + size) // 3


def pair_energy(values: tuple) -> int:
    multiplicities = Counter(a - b for a in values for b in values)
    return sum(count * count for count in multiplicities.values())


def missing_completions(values: tuple) -> int:
    support = set(values)
    return sum(
        x + z - y not in support
        for x, y, z in combinations(sorted(values), 3)
    )


def schur_count(values: tuple) -> int:
    support = set(values)
    return sum(x + y in support for x in values for y in values)


def is_progression(values: tuple) -> bool:
    if len(values) <= 2:
        return True
    gaps = [b - a for a, b in zip(values, values[1:])]
    return len(set(gaps)) == 1


def is_second_model(values: tuple) -> bool:
    if len(values) < 3:
        return False
    gaps = [b - a for a, b in zip(values, values[1:])]
    step = min(gaps)
    return gaps in (
        [step] * (len(values) - 2) + [2 * step],
        [2 * step] + [step] * (len(values) - 2),
    )


def check_set(values: tuple) -> tuple[int, int]:
    size = len(values)
    energy = pair_energy(values)
    maximum = maximum_energy(size)
    deficit = missing_completions(values)
    require(maximum - energy == 4 * deficit, f"defect identity: {values}")
    require(energy % 4 == size % 4, f"congruence: {values}")
    require((deficit == 0) == is_progression(values), f"maximum: {values}")

    if size >= 2:
        prefix, endpoint = values[:-1], values[-1]
        reflected = tuple(sorted(endpoint - x for x in prefix))
        endpoint_schur = schur_count(reflected)
        recurrence = pair_energy(prefix) + 4 * size - 3 + 4 * endpoint_schur
        require(energy == recurrence, f"endpoint recurrence: {values}")
        endpoint_deficit = (size - 1) * (size - 2) // 2 - endpoint_schur
        require(
            (endpoint_deficit == 0) == is_progression(values),
            f"zero endpoint defect: {values}",
        )
        if size >= 5 and endpoint_deficit == 1:
            require(is_second_model(values), f"unit endpoint defect: {values}")

    if size >= 3 and not is_progression(values):
        require(deficit >= size - 2, f"first gap: {values}")
    if size >= 5:
        require(
            (deficit == size - 2) == is_second_model(values),
            f"second equality classification: {values}",
        )
        if not is_progression(values) and not is_second_model(values):
            require(deficit >= 2 * size - 6, f"third gap: {values}")
    return energy, deficit


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-coordinate", type=int, default=14)
    parser.add_argument("--max-size", type=int, default=9)
    parser.add_argument("--schur-max", type=int, default=16)
    parser.add_argument("--schur-size", type=int, default=8)
    parser.add_argument("--one-hole-max", type=int, default=24)
    args = parser.parse_args()
    require(5 <= args.max_size <= args.max_coordinate, "invalid energy bounds")
    require(4 <= args.schur_size < args.schur_max, "invalid Schur bounds")
    require(args.one_hole_max >= 5, "one-hole bound must be at least 5")

    energy_rows = []
    total_sets = 0
    for size in range(1, args.max_size + 1):
        energies = Counter()
        second_count = 0
        third_count = 0
        for tail in combinations(range(1, args.max_coordinate + 1), size - 1):
            values = (0,) + tail
            energy, deficit = check_set(values)
            energies[energy] += 1
            if size >= 5:
                second_count += deficit == size - 2
                third_count += deficit == 2 * size - 6
        count = sum(energies.values())
        total_sets += count
        top_three = sorted(energies, reverse=True)[:3]
        if size >= 5:
            maximum = maximum_energy(size)
            expected = [maximum, maximum - 4 * (size - 2), maximum - 8 * (size - 3)]
            require(top_three == expected, f"attained first three levels at size {size}")
        energy_rows.append(
            {
                "size": size,
                "sets_checked": count,
                "distinct_energies": len(energies),
                "largest_three_observed": top_three,
                "second_level_sets": second_count if size >= 5 else None,
                "third_level_sets": third_count if size >= 5 else None,
            }
        )

    schur_rows = []
    total_schur = 0
    for size in range(1, args.schur_size + 1):
        checked = zero_count = one_count = 0
        for values in combinations(range(1, args.schur_max + 1), size):
            checked += 1
            defect = size * (size - 1) // 2 - schur_count(values)
            require(defect >= 0, f"Schur maximum: {values}")
            step = values[0]
            zero_model = tuple(step * k for k in range(1, size + 1))
            require((defect == 0) == (values == zero_model), f"Schur equality: {values}")
            zero_count += defect == 0
            one_count += defect == 1
            if size >= 4:
                one_model = tuple(step * k for k in list(range(1, size)) + [size + 1])
                require(
                    (defect == 1) == (values == one_model),
                    f"unit Schur classification: {values}",
                )
        total_schur += checked
        schur_rows.append(
            {
                "size": size,
                "sets_checked": checked,
                "zero_defect_sets": zero_count,
                "unit_defect_sets": one_count,
                "unit_classification_asserted": size >= 4,
            }
        )

    one_hole_count = 0
    for size in range(2, args.one_hole_max + 1):
        for hole in range(1, size):
            values = tuple(x for x in range(size + 1) if x != hole)
            energy, deficit = check_set(values)
            expected = hole * (size - hole) - min(hole, size - hole)
            require(deficit == expected, f"one-hole formula: m={size}, j={hole}")
            one_hole_count += 1

    rational_fixtures = [
        (Fraction(0), Fraction(1), Fraction(17, 11)),
        tuple(Fraction(-7, 3) + Fraction(5, 7) * x for x in (0, 1, 2, 3, 5)),
        tuple(Fraction(4, 5) + Fraction(2, 9) * x for x in (0, 2, 3, 4, 5)),
        tuple(Fraction(2, 3) + Fraction(11, 13) * x for x in (0, 1, 3, 4, 5)),
        (Fraction(0), Fraction(1), Fraction(101), Fraction(102)),
    ]
    for values in rational_fixtures:
        check_set(values)

    small_exception = (0, 1, 4, 5)
    require(pair_energy(small_exception) == 36, "four-point exception energy")
    require(not is_second_model(small_exception), "four-point exception geometry")
    schur_exception = (1, 3, 4)
    require(3 - schur_count(schur_exception) == 1, "three-point Schur exception")
    cyclic_counts = Counter((a - b) % 3 for a in range(3) for b in range(3))
    cyclic_energy = sum(count * count for count in cyclic_counts.values())
    require(cyclic_energy == 27 > maximum_energy(3), "torsion counterexample")

    report = {
        "status": "all checks passed",
        "arithmetic": "exact integers and fractions; Python standard library only",
        "python_version": platform.python_version(),
        "energy_exhaustion": {
            "domain": f"all subsets of {{0,...,{args.max_coordinate}}} containing 0",
            "sizes": [1, args.max_size],
            "sets_checked": total_sets,
            "rows": energy_rows,
        },
        "positive_schur_exhaustion": {
            "domain": f"all subsets of {{1,...,{args.schur_max}}}",
            "sizes": [1, args.schur_size],
            "sets_checked": total_schur,
            "rows": schur_rows,
        },
        "one_hole_formula": {
            "size_range": [2, args.one_hole_max],
            "all_interior_holes": True,
            "sets_checked": one_hole_count,
        },
        "rational_and_large_gap_fixtures_checked": len(rational_fixtures),
        "necessary_hypotheses": {
            "four_point_second_level_exception": list(small_exception),
            "four_point_exception_energy": 36,
            "three_point_unit_schur_exception": list(schur_exception),
            "full_cyclic_group_order_3_energy": cyclic_energy,
            "torsion_free_maximum_at_size_3": maximum_energy(3),
        },
        "limitations": [
            "Exhaustion is restricted to the explicitly recorded finite boxes.",
            "No complete third-level equality classification is asserted or tested.",
            "These diagnostics complement the proofs; they are not formal verification.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(
        f"Passed: {total_sets} energy sets, {total_schur} positive Schur sets, "
        f"{one_hole_count} one-hole sets, and {len(rational_fixtures)} exact fixtures."
    )
    print(f"Report: {args.output.resolve()}")


if __name__ == "__main__":
    main()
