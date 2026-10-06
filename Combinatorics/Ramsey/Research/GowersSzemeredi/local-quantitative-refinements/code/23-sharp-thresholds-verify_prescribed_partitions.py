#!/usr/bin/env python3
"""Exact finite checks for prescribed-length linear phase partitions.

Only Python's standard library is required. These finite checks support, but
do not replace, the proofs in the article. Run with --output FILE to retain
the JSON report. No network access is used.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from heapq import heappop, heappush
from itertools import product
import json
from math import ceil, gcd, isqrt, prod
from pathlib import Path


def circle_norm(value: Fraction) -> Fraction:
    residue = value % 1
    return min(residue, 1 - residue)


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def next_prime(bound: Fraction | int) -> int:
    n = int(bound) + 1
    while not is_prime(n):
        n += 1
    return n


def representability(lengths: tuple[int, ...], bound: int) -> list[bool]:
    reachable = [False] * (bound + 1)
    reachable[0] = True
    for n in range(1, bound + 1):
        reachable[n] = any(n >= s and reachable[n - s] for s in lengths)
    return reachable


def conductor_by_residues(lengths: tuple[int, ...]) -> int:
    """Apéry-set calculation; also checked against independent integer DP."""
    if gcd(*lengths) != 1:
        raise ValueError("The length set must have gcd one.")
    modulus = min(lengths)
    distances: list[int | None] = [None] * modulus
    distances[0] = 0
    pending = [(0, 0)]
    while pending:
        distance, residue = heappop(pending)
        if distances[residue] != distance:
            continue
        for length in lengths:
            target = (residue + length) % modulus
            candidate = distance + length
            if distances[target] is None or candidate < distances[target]:
                distances[target] = candidate
                heappush(pending, (candidate, target))
    assert all(value is not None for value in distances)
    return max(value for value in distances if value is not None) - modulus + 1


def check_conductors() -> dict:
    tested = 0
    for lower in range(2, 61):
        for width in range(1, lower):
            lengths = tuple(range(lower, lower + width + 1))
            expected = lower * ceil(Fraction(lower - 1, width))
            assert conductor_by_residues(lengths) == expected
            reachable = representability(lengths, expected + 2 * max(lengths))
            assert not reachable[expected - 1]
            assert all(reachable[expected:])
            tested += 1
    examples = []
    for lengths in ((4, 7), (4, 6, 9), (5, 7), (5, 8, 11)):
        conductor = conductor_by_residues(lengths)
        reachable = representability(lengths, conductor + 3 * max(lengths))
        assert not reachable[conductor - 1]
        assert all(reachable[conductor:])
        examples.append({"lengths": lengths, "conductor": conductor})
    return {"interval_length_sets": tested, "other_examples": examples}


def check_mixed_radix() -> dict:
    families = 0
    nonzero_residues = 0
    for dimensions in range(1, 4):
        for radices in product(range(2, 8), repeat=dimensions):
            denominators = []
            denominator = 1
            for radix in radices:
                denominator *= radix
                denominators.append(denominator)
            for difference in range(1, denominator):
                first = next(
                    i for i, base in enumerate(denominators)
                    if difference % base
                )
                norm = circle_norm(Fraction(difference, denominators[first]))
                assert norm >= Fraction(1, radices[first])
                nonzero_residues += 1
            families += 1
    return {"radix_families": families, "nonzero_residues_checked": nonzero_residues}


def check_volume_approximation() -> dict:
    tested = 0
    examples = []
    for modulus, tolerances in (
        (37, (Fraction(1, 4), Fraction(1, 5))),
        (37, (Fraction(2, 7), Fraction(1, 5))),
        (19, (Fraction(2, 5), Fraction(3, 7))),
        (23, (Fraction(1, 3),)),
    ):
        inverse_volume = 1 / prod(tolerances)
        bound = ceil(inverse_volume) - 1
        largest_first_return = 0
        for coefficients in product(range(modulus), repeat=len(tolerances)):
            first_return = next(
                (difference for difference in range(1, bound + 1)
                 if all(circle_norm(Fraction(difference * a, modulus)) <= delta
                        for a, delta in zip(coefficients, tolerances))),
                None,
            )
            assert first_return is not None
            largest_first_return = max(largest_first_return, first_return)
            tested += 1
        examples.append({
            "modulus": modulus,
            "coordinate_tolerances": [str(delta) for delta in tolerances],
            "inverse_box_volume": str(inverse_volume),
            "guaranteed_difference_bound": bound,
            "largest_observed_first_return": largest_first_return,
        })
    return {"rational_phase_vectors": tested, "examples": examples}


def build_partition(
    interval_length: int,
    lengths: tuple[int, ...],
    slopes: tuple[Fraction, ...],
    tolerances: tuple[Fraction, ...],
) -> dict:
    conductor = conductor_by_residues(lengths)
    boxes = tuple(ceil(Fraction(max(lengths) - 1, 1) / e) for e in tolerances)
    grid_bound = prod(boxes)
    denominator_bound = ceil(Fraction(max(lengths) - 1) ** len(slopes) / prod(tolerances)) - 1
    assert interval_length >= conductor * denominator_bound
    difference = next(
        d for d in range(1, denominator_bound + 1)
        if all(circle_norm(d * a) <= e / (max(lengths) - 1)
               for a, e in zip(slopes, tolerances))
    )
    largest_chain = ceil(Fraction(interval_length, difference))
    previous: list[int | None] = [None] * (largest_chain + 1)
    previous[0] = 0
    for n in range(1, largest_chain + 1):
        previous[n] = next(
            (s for s in lengths if n >= s and previous[n - s] is not None), None
        )
    covered = [False] * interval_length
    cells = 0
    cell_sizes = set()
    for residue in range(difference):
        chain_size = (interval_length - 1 - residue) // difference + 1
        assert chain_size >= conductor and previous[chain_size] is not None
        decomposition = []
        remaining = chain_size
        while remaining:
            length = previous[remaining]
            assert length is not None
            decomposition.append(length)
            remaining -= length
        position = residue
        for length in decomposition:
            assert length in lengths
            for slope, epsilon in zip(slopes, tolerances):
                assert (length - 1) * circle_norm(difference * slope) <= epsilon
            for index in range(length):
                point = position + index * difference
                assert 0 <= point < interval_length and not covered[point]
                covered[point] = True
            position += length * difference
            cells += 1
            cell_sizes.add(length)
    assert all(covered)
    return {
        "interval_length": interval_length,
        "lengths": lengths,
        "conductor": conductor,
        "denominator_bound": denominator_bound,
        "grid_denominator_bound": grid_bound,
        "chosen_difference": difference,
        "cell_count": cells,
        "observed_cell_sizes": sorted(cell_sizes),
        "points_covered_exactly_once": sum(covered),
    }


def check_constructive_partitions() -> list[dict]:
    examples = [
        ((3, 4), (Fraction(17, 997), Fraction(211, 997)), (Fraction(1, 4),) * 2),
        ((5, 7), (Fraction(73, 101), Fraction(19, 257)), (Fraction(1, 4),) * 2),
        ((4, 6, 9), (Fraction(17, 137),), (Fraction(1, 5),)),
        ((3, 4), (Fraction(17, 131), Fraction(37, 131)),
         (Fraction(1, 5), Fraction(2, 7))),
    ]
    results = []
    for lengths, slopes, tolerances in examples:
        conductor = conductor_by_residues(lengths)
        volume_bound = ceil(Fraction(max(lengths) - 1) ** len(slopes) / prod(tolerances)) - 1
        results.append(build_partition(conductor * volume_bound, lengths, slopes, tolerances))
    return results


def check_prime_obstruction() -> dict:
    lower = 4
    lengths = (4, 5)
    tolerances = (Fraction(1, 4), Fraction(1, 4))
    radices = [ceil(Fraction(lower - 1, 1) / e) - 1 for e in tolerances]
    denominators = []
    current = 1
    for radix in radices:
        current *= radix
        denominators.append(current)
    period = current
    conductor = conductor_by_residues(lengths)
    gap = conductor - 1
    interval_length = period * gap
    margins = [Fraction(1, m) - e / (lower - 1) for m, e in zip(radices, tolerances)]
    margin = min(margins)
    prime_bound = max(
        interval_length,
        Fraction(interval_length - 1, 2 * (lower - 1)) / margin,
    )
    prime = next_prime(prime_bound)
    coefficients = [(2 * prime + denominator) // (2 * denominator) for denominator in denominators]
    for coefficient, denominator in zip(coefficients, denominators):
        assert abs(Fraction(coefficient, prime) - Fraction(1, denominator)) <= Fraction(1, 2 * prime)
    difference_bound = (interval_length - 1) // (lower - 1)
    necessary_differences = []
    actual_by_length = {}
    for difference in range(1, difference_bound + 1):
        if all(circle_norm(Fraction(difference * a, prime)) <= e / (lower - 1)
               for a, e in zip(coefficients, tolerances)):
            assert difference % period == 0
            necessary_differences.append(difference)
    for length in lengths:
        actual = []
        for difference in range(1, (interval_length - 1) // (length - 1) + 1):
            # Translation invariance means checking these differences checks
            # every permitted starting point. Metric-flatness is weaker than
            # arc-flatness, so this also rules out all forbidden arc-flat APs.
            if all(circle_norm(Fraction(index * difference * a, prime)) <= e
                   for a, e in zip(coefficients, tolerances)
                   for index in range(1, length)):
                assert difference % period == 0
                actual.append(difference)
        actual_by_length[str(length)] = actual
    reachable = representability(lengths, gap)
    assert not reachable[gap]
    assert all(
        (interval_length - 1 - residue) // period + 1 == gap
        for residue in range(period)
    )
    sharp_interval_length = period * conductor - 1
    sharp_chain_sizes = [
        (sharp_interval_length - 1 - residue) // period + 1
        for residue in range(period)
    ]
    assert sharp_chain_sizes.count(conductor - 1) == 1
    assert sharp_chain_sizes.count(conductor) == period - 1
    return {
        "lengths": lengths,
        "tolerances": [str(e) for e in tolerances],
        "radices": radices,
        "period": period,
        "conductor": conductor,
        "unrepresentable_points_per_residue": gap,
        "interval_length": interval_length,
        "margin": str(margin),
        "prime": prime,
        "modular_coefficients": coefficients,
        "all_necessary_differences": necessary_differences,
        "all_metric_flat_differences_by_length": actual_by_length,
        "sharper_rational_witness_interval": sharp_interval_length,
        "exact_eventual_threshold_for_rational_vector": period * conductor,
        "no_partition_certificate": "Every permitted cell is contained in one residue class modulo the period; each such class has unrepresentable cardinality.",
    }


def check_packing_formula() -> dict:
    # For all rigid examples, the exact optimum reduces to the sum of the
    # greatest semigroup elements below the independent residue sizes.
    tests = 0
    for lengths in ((3, 4), (4, 5), (4,), (4, 6), (5, 7)):
        period = 7
        reachable = representability(lengths, 150)
        floors = []
        current = 0
        for n, representable in enumerate(reachable):
            if representable:
                current = n
            floors.append(current)
        for interval_length in range(1, 1001):
            quotient, remainder = divmod(interval_length, period)
            formula = (period - remainder) * floors[quotient] + remainder * floors[quotient + 1]
            direct = sum(
                floors[(interval_length - 1 - residue) // period + 1]
                for residue in range(min(period, interval_length))
            )
            assert formula == direct
            tests += 1
    partial_tests = 0
    for lower in range(2, 51):
        for eta in (Fraction(1, 2), Fraction(1, 5), Fraction(1, 10), Fraction(1, 100)):
            barrier = Fraction(lower - 1, 1) / eta
            k = ceil((barrier + 1) / lower) - 1
            gap_size = k * lower - 1
            assert barrier - lower <= gap_size < barrier
            assert gap_size % lower == lower - 1
            assert Fraction(lower - 1, gap_size) > eta
            partial_tests += 1
    return {"packing_formula_instances": tests, "partial_coverage_gap_choices": partial_tests}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write this JSON report to a file as well.")
    args = parser.parse_args()
    report = {
        "status": "all exact assertions passed",
        "arithmetic": "integers and fractions.Fraction; no floating-point decisions",
        "conductor_checks": check_conductors(),
        "mixed_radix_checks": check_mixed_radix(),
        "volume_approximation_checks": check_volume_approximation(),
        "constructive_partitions": check_constructive_partitions(),
        "prime_obstruction": check_prime_obstruction(),
        "packing_checks": check_packing_formula(),
        "scope": "Finite regression and certificate checks; the article's proofs establish the general statements.",
    }
    encoded = json.dumps(report, indent=2)
    if args.output:
        args.output.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)


if __name__ == "__main__":
    main()
